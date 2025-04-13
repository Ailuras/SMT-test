bash scripts/bench_preprocess.sh \
    --input-dir /home/hanrui/SMTLIB/QF_SLIA \
    --excel-dir charts \
    --excel-file QF_SLIA.xlsx

bash scripts/bench_preprocess.sh --input-dir /home/hanrui/SMTLIB/QF_SLIA --excel-dir charts --excel-file QF_SLIA.xlsx

bash scripts/bench_solve.sh --input-dir /home/hanrui/SMTLIB/QF_SLIA --output-dir results --task cvc5 --solver cvc5 --timeout 10 --parallel 20 --excel-dir charts --excel-file QF_SLIA.xls

bash scripts/bench_solve.sh --input-dir /home/hanrui/SMTLIB/QF_SLIA --output-dir results --task z3 --solver z3 --timeout 10 --parallel 20 --excel-dir charts --excel-file QF_SLIA.xls

bash scripts/bench_solve.sh --input-dir /home/hanrui/SMTLIB/QF_SLIA --output-dir results --task z3-noodler --solver z3-noodler --timeout 10 --parallel 20 --excel-dir charts --excel-file QF_SLIA.xls

