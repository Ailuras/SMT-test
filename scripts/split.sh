#！/bin/bash
# ./split.sh QF_NRA_part_new 10

number=$2

function split() {
    index=1
    name=1
    if [ ! -d "$@_$name" ];then
        mkdir $@_$name
    fi
    for file in $@/*; do
        mv $file $@_$name
        index=$[ $index + 1 ]
        if [[ $index -gt $[ $number * $name ] ]];then
            name=$[ $name + 1 ]
            if [ ! -d "$@_$name" ];then
                mkdir $@_$name
            fi
        fi
    done
    rm -rf $@
}

function splitAll() {
    for folder in $@/*;do 
        # echo `ls -lR $folder | grep "^-"| wc -l`
        state=-1
        for file in $folder/*;do
            if test -f $file;then
                state=0
                break
            fir
            if test -d $file;then
                state=1
                break
            fi
        done
        if [ $state -eq 0 ];then
            # ----- modifiy here -----
            echo $folder
            echo `ls -lR $folder | grep "^-"| wc -l`
            if [[ `ls -lR $folder | grep "^-"| wc -l` -gt $number ]];then
                split $folder
            fi
        fi
        if [ $state -eq 1 ];then
            splitAll $folder
        fi
    done
}

splitAll $1