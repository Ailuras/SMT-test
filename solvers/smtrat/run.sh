cd solvers/smtrat/bin
ulimit -t $2
LD_PRELOAD=libmimalloc.so ./smtrat ../../../$1 2>/dev/null
cd ../../..