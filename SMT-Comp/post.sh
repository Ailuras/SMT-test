#！/bin/bash
# 路径标准化
# post_process result

function post_process() {
    if test -d $@;then
        for file in $@/*;do 
            post_process $file
        done
    fi
    if test -f $@;then
        sed -i -r 's/\.\.\/\.\.\///g' $@
        sed -i -r 's/\.\.\///g' $@
        sed -i -r 's/_[0-9]+\//\//g' $@
        sed -i -r 's/temp\///g' $@
        sed -i -r 's/_split//g' $@
        sed -i -r 's/_hard//g' $@
        sed -i -r 's/_part_new//g' $@
    fi
}

post_process $1