.PHONY: all
all: test

.PHONY: build
build:
	cd charon && make

SRC = $(TESTS)/src
OPTIONS = --dest $(TESTS)/llbc

.PHONY: build-tests
build-tests:
	cd tests && make

.PHONY: build-tests-nll
build-tests-nll:
	cd tests-nll && make

.PHONY: test
test: build build-tests build-tests-nll \
	test-nested_borrows test-no_nested_borrows test-loops test-hashmap \
	test-paper test-hashmap_main \
	test-matches test-matches_duplicate test-external \
        test-constants \
	test-nll-betree_nll test-nll-betree_main

test-nested_borrows: OPTIONS += --no-code-duplication
test-no_nested_borrows: OPTIONS += --no-code-duplication
test-loops: OPTIONS += --no-code-duplication
#test-hashmap: OPTIONS += --no-code-duplication
#test-hashmap_main: OPTIONS += --no-code-duplication
test-hashmap_main: OPTIONS += --opaque=hashmap_utils
test-paper: OPTIONS += --no-code-duplication
test-constants: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
test-matches:
test-external: OPTIONS += --no-code-duplication
test-matches_duplicate:
#test-nll-betree_nll: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
test-nll-betree_main:
test-nll-betree_main: OPTIONS += --opaque=betree_utils

.PHONY: test-%
test-%: TESTS=../tests
test-%:
	cd charon && cargo run $(SRC)/$*.rs $(OPTIONS)
# I would like to do this, however there is a problem when loading libstd.so.
# I guess we need to indicate the path to the installed Rust library, sth?
#	charon/target/debug/charon $(SRC)/$*.rs $(OPTIONS)

.PHONY: test-nll-%
test-nll-%: TESTS=../tests-nll
test-nll-%: OPTIONS += --nll
test-nll-%:
	cd charon && cargo run $(SRC)/$*.rs $(OPTIONS)
