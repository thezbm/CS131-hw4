SUBMIT := $(shell cat submit_zip_contents.txt)
HWNAME := hw4
TIMESTAMP := $(shell /bin/date "+%Y-%m-%d-%H:%M:%S")
ZIPNAME := $(HWNAME)-submit-$(TIMESTAMP).zip

.PHONY: all oatc test clean zip

all: oatc

oatc: 
	dune build
	@cp bin/main.exe oatc

test: oatc
	./oatc --test

utop:
	dune utop

zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)

clean:
	dune clean
	rm -rf oatc ocamlbin bin/main.exe

# 
