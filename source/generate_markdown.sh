#! /bin/bash

mkdir markdown

for file in `ls *.lagda`; do
    echo "Writing $(basename $file .lagda).lagda.md..."
    cat $file | ./markdownify.sh > markdown/$(basename $file .lagda).lagda.md
done
