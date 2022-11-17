#！/bin/bash
# ./assign.sh 20161105-Sturm-MBO 1 0.0000001
# ./assign.sh QF_NRA_MBO 4 0.0000001

folder=$1
number=$2
value=$3

for file in $folder/*;do
    sed -i '/(assert (= [a-z][0-9].*))/d' $file
    var=$(sed -n 's/.*declare-const \([a-z][0-9]\) Real.*/\1/p' $file)
    index=0
    for i in ${var[@]};do
        if [ $index -lt $number ];then
            sed -i "/(check-sat)/i\(assert (= ${i} ${value}))" $file
        fi
        index=$[ $index + 1 ]
    done
done