find . -type f -name Makefile -print0 | xargs -0 sed -i "s/-Q\s\([^ ]*\)\s$1/-Q \1 $2.$1/g" "${@:3}"
find . -type f -name Makefile -print0 | xargs -0 sed -i "s/-R\s\([^ ]*\)\s$1/-R \1 $2.$1/g" "${@:3}"
echo "s/From $1\(.*\) Require/From $2.$1\1 Require/g" >> rename_bedrock2.txt
echo ":A; s/Import\(.*\)\s$1\./Import\1 $2.$1./g; tA" >> rename_bedrock2.txt
echo ":B; s/Export\(.*\)\s$1\./Export\1 $2.$1./g; tB" >> rename_bedrock2.txt
echo ":C; s/Require\(.*\)\s$1\./Require\1 $2.$1./g; tC" >> rename_bedrock2.txt
./refactor_sed.sh -f rename_bedrock2.txt
rm rename_bedrock2.txt

