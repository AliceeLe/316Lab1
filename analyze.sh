#!/usr/bin/env bash
set -euo pipefail

die() {
  echo "error: $*" >&2
  exit 1
}

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "missing required command: $1"
}

is_wsl() {
  # WSL 1/2 both typically include "microsoft" in the kernel release/version.
  uname -r 2>/dev/null | tr '[:upper:]' '[:lower:]' | grep -q "microsoft" && return 0
  grep -qi "microsoft" /proc/version 2>/dev/null && return 0
  return 1
}

usage() {
  cat <<'EOF'
Usage:
  scripts/analyze.sh [-u URL] [-f FILE] [--json] [--debug] [--max-wait-seconds N]
  scripts/analyze.sh --login [-u URL]
  scripts/analyze.sh --logout
  scripts/analyze.sh --doctor

Defaults:
  URL  = https://safetychecker.net
  FILE = example.c0
  N    = 330

Examples:
  scripts/analyze.sh
  scripts/analyze.sh -u http://localhost:8000 -f example.c0
  scripts/analyze.sh -f path/to/submission.c0
  scripts/analyze.sh --login
EOF
}

URL="https://safetychecker.net"
FILE="example.c0"
ACCEPT="text/plain"
DEBUG="0"
MAX_WAIT_SECONDS="330"
LOGIN_ONLY="0"
LOGOUT_ONLY="0"
DOCTOR_ONLY="0"
TOKEN_OVERRIDE=""

config_home="${XDG_CONFIG_HOME:-$HOME/.config}"
TOKEN_FILE="${config_home}/lab1-refsol/token"

while [[ $# -gt 0 ]]; do
  case "$1" in
    -u|--url) URL="$2"; shift 2 ;;
    -f|--file) FILE="$2"; shift 2 ;;
    --json) ACCEPT="application/json"; shift ;;
    --debug) DEBUG="1"; shift ;;
    --max-wait-seconds) MAX_WAIT_SECONDS="$2"; shift 2 ;;
    --login) LOGIN_ONLY="1"; shift ;;
    --logout) LOGOUT_ONLY="1"; shift ;;
    --doctor) DOCTOR_ONLY="1"; shift ;;
    --token) TOKEN_OVERRIDE="$2"; shift 2 ;;
    --token-file) TOKEN_FILE="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage; exit 1 ;;
  esac
done

JSON_PARSER=""
choose_json_parser() {
  if command -v python3 >/dev/null 2>&1; then
    JSON_PARSER="python3"
    return 0
  fi
  if command -v python >/dev/null 2>&1; then
    JSON_PARSER="python"
    return 0
  fi
  if command -v node >/dev/null 2>&1; then
    JSON_PARSER="node"
    return 0
  fi
  if command -v jq >/dev/null 2>&1; then
    JSON_PARSER="jq"
    return 0
  fi
  return 1
}

json_get_key() {
  local key="$1"
  case "$JSON_PARSER" in
    python3|python)
      "$JSON_PARSER" -c 'import json,sys; obj=json.load(sys.stdin); v=obj.get(sys.argv[1],""); print("" if v is None else v)' "$key"
      ;;
    node)
      node -e 'const fs=require("fs"); const key=process.argv[1]; const obj=JSON.parse(fs.readFileSync(0,"utf8")); const v=obj && obj[key]; process.stdout.write(v==null?"":String(v));' "$key"
      ;;
    jq)
      jq -r --arg k "$key" '.[$k] // ""'
      ;;
    *)
      die "internal: JSON parser not configured"
      ;;
  esac
}

open_browser() {
  local url="$1"
  if is_wsl; then
    if command -v wslview >/dev/null 2>&1; then
      wslview "$url" >/dev/null 2>&1 || true
      return 0
    fi
    if command -v cmd.exe >/dev/null 2>&1; then
      cmd.exe /c start "" "$url" >/dev/null 2>&1 || true
      return 0
    fi
  fi
  if command -v open >/dev/null 2>&1; then
    open "$url" >/dev/null 2>&1 || true
    return 0
  fi
  if command -v xdg-open >/dev/null 2>&1; then
    xdg-open "$url" >/dev/null 2>&1 || true
    return 0
  fi
  return 1
}

save_token() {
  local token="$1"
  mkdir -p "$(dirname "$TOKEN_FILE")"
  printf '%s\n' "$token" >"$TOKEN_FILE"
  chmod 600 "$TOKEN_FILE" 2>/dev/null || true
}

read_token_file() {
  if [[ -f "$TOKEN_FILE" ]]; then
    tr -d '\r\n \t' <"$TOKEN_FILE" || true
  fi
}

get_token() {
  if [[ -n "${LAB1_REFSOL_TOKEN:-}" ]]; then
    printf '%s' "${LAB1_REFSOL_TOKEN}"
    return 0
  fi
  if [[ -n "$TOKEN_OVERRIDE" ]]; then
    printf '%s' "$TOKEN_OVERRIDE"
    return 0
  fi
  local tok
  tok="$(read_token_file)"
  if [[ -n "$tok" ]]; then
    printf '%s' "$tok"
    return 0
  fi
  return 1
}

do_login() {
  local cli_url="${URL%/}/cli"
  echo "Authenticate via Google in your browser to get a CLI token:"
  echo "  $cli_url"
  open_browser "$cli_url" || true
  echo
  read -r -p "Paste token here: " tok
  tok="$(printf '%s' "$tok" | tr -d '\r\n \t')"
  if [[ -z "$tok" ]]; then
    echo "Missing token." >&2
    exit 1
  fi
  save_token "$tok"
  echo "Saved token to $TOKEN_FILE"
}

doctor() {
  need_cmd bash
  need_cmd curl
  need_cmd date
  need_cmd mktemp
  need_cmd grep
  need_cmd sed
  need_cmd awk
  need_cmd tr
  need_cmd head
  need_cmd sleep

  if ! choose_json_parser; then
    die "missing JSON parser: install one of python3, python, node, or jq"
  fi

  echo "OK: dependencies found"
  echo "  curl: $(command -v curl)"
  echo "  json: $JSON_PARSER"
  echo "  token file: $TOKEN_FILE"
  if is_wsl; then
    echo "  env: WSL"
  else
    echo "  env: $(uname -s 2>/dev/null || echo unknown)"
  fi
}

if [[ "$DOCTOR_ONLY" == "1" ]]; then
  doctor
  exit 0
fi

need_cmd curl
need_cmd date
need_cmd mktemp
need_cmd grep
need_cmd sed
need_cmd awk
need_cmd tr
need_cmd head
need_cmd sleep
choose_json_parser || die "missing JSON parser: install one of python3, python, node, or jq"

if [[ "$LOGOUT_ONLY" == "1" ]]; then
  rm -f "$TOKEN_FILE"
  echo "Removed token file: $TOKEN_FILE"
  exit 0
fi

if [[ "$LOGIN_ONLY" == "1" ]]; then
  do_login
  exit 0
fi

if [[ ! -f "$FILE" ]]; then
  echo "File not found: $FILE" >&2
  exit 1
fi

TOKEN="$(get_token || true)"
if [[ -z "$TOKEN" ]]; then
  do_login
  TOKEN="$(get_token || true)"
fi
if [[ -z "$TOKEN" ]]; then
  echo "Unable to load token." >&2
  exit 1
fi

QS=""
if [[ "$DEBUG" == "1" ]]; then
  QS="?debug=1"
fi

# Avoid 504s from upstream proxies (e.g., Cloudflare) by using the async API.
# 1) Submit job (fast)
# 2) Poll for result (up to MAX_WAIT_SECONDS)
tmp_job="$(mktemp 2>/dev/null || mktemp -t lab1-refsol-job.XXXXXX)"
tmp_poll=""
trap 'rm -f "$tmp_job" "${tmp_poll:-}"' EXIT
code="$(
  curl -sS \
    -H "Accept: application/json" \
    -H "Authorization: Bearer ${TOKEN}" \
    -F "file=@${FILE};type=text/plain" \
    -o "$tmp_job" \
    -w "%{http_code}" \
    "${URL%/}/analyze-async"
)"
if [[ "$code" != "200" ]]; then
  echo "submit failed (HTTP $code):" >&2
  sed -e 's/\r$//' "$tmp_job" >&2 || true
  exit 1
fi
JOB_ID="$(sed -e 's/\r$//' "$tmp_job" | json_get_key "job_id" | tr -d '\r\n \t')"
if [[ -z "$JOB_ID" ]]; then
  echo "submit failed: missing job_id" >&2
  sed -e 's/\r$//' "$tmp_job" >&2 || true
  exit 1
fi

DEADLINE=$(( $(date +%s) + MAX_WAIT_SECONDS ))
while true; do
  NOW=$(date +%s)
  if (( NOW > DEADLINE )); then
    echo "submission timed out" >&2
    exit 124
  fi

  tmp_poll="$(mktemp 2>/dev/null || mktemp -t lab1-refsol-poll.XXXXXX)"
  code="$(curl -sS -H "Accept: $ACCEPT" -H "Authorization: Bearer ${TOKEN}" -o "$tmp_poll" -w "%{http_code}" "${URL%/}/analyze-async/${JOB_ID}${QS}")"
  body="$(sed -e 's/\r$//' "$tmp_poll")"
  rm -f "$tmp_poll"
  tmp_poll=""

  # Pending jobs return JSON {"status":"pending",...} with 200
  if [[ "$ACCEPT" == "application/json" ]]; then
    if [[ "$code" == "200" ]] && printf '%s' "$body" | json_get_key "status" 2>/dev/null | tr -d '\r\n \t' | grep -qx "pending"; then
      sleep 1
      continue
    fi
  else
    # Text mode: pending returns JSON {"status":"pending",...}.
    if [[ "$code" == "200" ]] && printf '%s' "$body" | head -c 1 | grep -q '{'; then
      status="$(printf '%s' "$body" | json_get_key "status" 2>/dev/null || true)"
      status="$(printf '%s' "$status" | tr -d '\r\n \t')"
      if [[ "$status" == "pending" ]]; then
        sleep 1
        continue
      fi
      # Some non-pending JSON response while requesting text/plain likely indicates an error.
      echo "poll failed: unexpected JSON response" >&2
      printf '%s\n' "$body" >&2
      exit 1
    fi
  fi

  if [[ "$code" == "504" ]]; then
    echo "submission timed out" >&2
    exit 124
  fi

  if [[ "$code" != "200" ]]; then
    echo "poll failed (HTTP $code):" >&2
    printf '%s\n' "$body" >&2
    exit 1
  fi

  printf '%s' "$body"
  exit 0
done
