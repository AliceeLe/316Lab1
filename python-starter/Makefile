all: c0_vc

default: all

c0_vc:
	install ./c0_vc.sh $@

clean:
	rm -f c0_vc lab1.zip

SRC_DIRS := ./src
VENDOR_DIRS := ./vendor

FILES := \
	Makefile \
	requirements.txt \
	.gitignore \
	c0_vc.sh \
	$(shell find $(SRC_DIRS) -name '*.py') \
	$(shell find $(VENDOR_DIRS) -type f)

handin: lab1.zip

lab1.zip: $(FILES)
	zip $@ $^

.PHONY: clean native handin
