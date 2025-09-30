TEST_FUNS = $(wildcard *.fun)
TEST_OKS = $(patsubst %.fun,%.ok,${TEST_FUNS})
TEST_OUTS = $(patsubst %.fun,%.out,${TEST_FUNS})
TEST_DIFFS = $(patsubst %.fun,%.diff,${TEST_FUNS})

fun : ${wildcard *.hs}
	ghc -o fun fun.hs -Werror


test : ${TEST_DIFFS};

${TEST_OUTS} : %.out : fun %.fun
	-./fun < $*.fun > $*.out 2>&1

${TEST_DIFFS} : %.diff : %.ok %.out
	@((diff $*.ok $*.out > $*.diff) && echo "$* ... pass") || (echo "$* ... fail")


test_names:
	@echo "${TEST_FUNS}"
	@echo "${TEST_OKS}"
	@echo "${TEST_OUTS}"


clean:
	rm -rf fun *.o *.hi *.diff *.out
