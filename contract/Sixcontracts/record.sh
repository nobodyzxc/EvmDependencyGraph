OYENTE=../../oyente.py
type $OYENTE >/dev/null 2>&1 || { echo >&2 "../../oyente.py not exist"; exit 1; }
if [ $# != 1 ];then echo 'give me type';fi
if [ "$1" == "weak" ];then
    TYPE="-cfg-weak"
elif [ "$1" == "gas" ];then
    TYPE="-cfg-gas"
elif [ "$1" == "nor" ];then
    TYPE="-cfg"
elif [ "$1" == "normal" ];then
    TYPE="-cfg"
else
    echo "no matched type"
    exit
fi

for i in ./*.sol ;do echo "processing $i"; $OYENTE $TYPE -p -s $i 2> ${i%.*}.txt;done
