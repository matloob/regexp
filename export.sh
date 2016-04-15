#!/bin/sh

FROM="$HOME/src/matloob.io/regexp"
TO="$HOME/go/src/regexp"

cp $FROM/*.go $TO/
cp $FROM/syntax/*.go $TO/syntax/

sed -i -e "s/matloob.io\///g" $TO/*.go