if [ $# != 1 ];then
    echo 'give me upload type'
fi

PWD=`pwd`
DIR=`basename $PWD`

if [ "$1" == "weak" ];then
    zip -R ${DIR}_${1}.zip *.txt "*/*.svg"
    # scp -r *.svg *.txt *_*/ s10410@cherry.cs.nccu.edu.tw:~s10410/public_html/static/$DIR/$1
else
    zip ${DIR}_${1}.zip *.svg *.txt
    scp *.svg *.txt s10410@cherry.cs.nccu.edu.tw:~s10410/public_html/static/$DIR/$1
fi
scp ${DIR}_${1}.zip s10410@cherry.cs.nccu.edu.tw:~s10410/public_html/static/$DIR/
