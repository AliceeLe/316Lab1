import os
import sys

# Prefer vendored dependencies (so the starter works out-of-the-box after `make`).
sys.path.append(os.path.join(os.path.dirname(__file__), "..", "vendor"))

from parse import file_parse
from wlp import check_safety


def print_and_exit(msg: str, code: int) -> None:
    try:
        print(msg)
    except BrokenPipeError:
        pass
    raise SystemExit(code)


def main() -> None:
    argv = sys.argv[1:]
    if len(argv) != 1:
        print_and_exit("error", 1)
    filename = argv[0]
    try:
        with open(filename, "r", encoding="utf-8") as f:
            src = f.read()
    except Exception:
        print_and_exit("error", 1)

    try:
        prog = file_parse(src)
    except Exception as e:
        _ = e
        print_and_exit("error", 1)

    try:
        ok = check_safety(prog)
    except NotImplementedError:
        print_and_exit("error", 1)
    except Exception as e:
        _ = e
        print_and_exit("error", 1)

    if ok:
        print_and_exit("valid", 0)
    else:
        print_and_exit("unsafe", 2)


if __name__ == "__main__":
    main()
