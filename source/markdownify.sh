#! /bin/bash

cat - | sed 's/\\\begin{code}\[hide\]/```agda/g' | sed 's/\\\begin{code}/```agda/g' | sed 's/\\\end{code}/```/g' | sed -E 's/\\\section\{([[:alnum:]|[:punct:][:blank:]]+)\}/\#\# \1/'
