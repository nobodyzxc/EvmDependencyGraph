for i in `ls *.sol`;do
    python ../../dg_main.py -b $i
    if [ $? -ne 0 ];then
        echo $i
        break
    fi
done
