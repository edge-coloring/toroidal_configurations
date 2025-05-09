#!/bin/bash
set -euxo pipefail
cd "$(dirname "$0")"

#
# bash loop.sh reducible/summary.csv reducible/conf nconfs/nconf
#

summary=$1
confdir=$2
outdir=$3

while IFS="," read f status csize conts; do
    confBaseName=$(basename $f | sed -e "s/log/conf/g")
    confFileName="$confdir/$confBaseName"
    if [ ! -e $confFileName ]; then
        continue
    fi
    if [ $status = "C" ]; then
        python3 loop.py "$confFileName" -o "$outdir" -e $(echo $conts | tr -d '"' | tr '+' ' ')
    fi
done < $summary 