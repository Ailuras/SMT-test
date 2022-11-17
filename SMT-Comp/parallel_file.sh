#！/bin/bash
# ./parallel_file.sh mbo_z3/1 1200 z3 1
time_t=$2
solver=$3
result=$4

index=1
function parallel() {
    # echo 'hh'
    for file in $@/*;do 
        nohup bash run.sh $file $time_t $solver > mbo_z3/result_$result/result_$index.log 2>&1 &
        index=$[ $index + 1 ]
    done
}

parallel $1