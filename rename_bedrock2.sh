./refactor_sed.sh -f rename_bedrock2.txt
find . -type f -name Makefile -print0 | xargs -0 sed -i "s/-Q \([^\s].*\) bedrock2/-Q \1 bedrock2A.bedrock2/g" "$@"
