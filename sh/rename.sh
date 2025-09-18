source sh/utility.sh

src=$(normalize $1)
echo src = $src

dst=$(normalize $2)
echo dst = $dst

srcFile=Lemma/${src//.//}.lean
echo srcFile = $srcFile

dstFile=Lemma/${dst//.//}.lean
echo dstFile = $dstFile

parent_path=$(dirname $dstFile)
echo mkdir -p $parent_path
mkdir -p $parent_path

echo mv $srcFile $dstFile
if [ -f $dstFile ]; then
    echo "error: $dstFile already exists"
    exit
fi
if [ ! -f $srcFile ]; then
    echo "error: $srcFile does not exist"
    exit
fi

mv $srcFile $dstFile

srcReg=${src//./\\.}
srcReg="\b$srcReg"
echo srcReg = $srcReg
submodule="((\.[a-z_]+)*(\b[^.]|$))"
echo find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/$srcReg$submodule/$dst\1/g" {} +
find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/$srcReg$submodule/$dst\1/g" {} +

package_src=$(echo $src | cut -d'.' -f1)
echo package_src = $package_src

package_dst=$(echo $dst | cut -d'.' -f1)
echo package_dst = $package_dst

lemmaNameSrcOrig=$(echo "$src" | cut -d'.' -f2-)
lemmaNameSrc=${lemmaNameSrcOrig//./\\.}
echo lemmaNameSrc = $lemmaNameSrc

lemmaNameDstOrig=$(echo "$dst" | cut -d'.' -f2-)
lemmaNameDst=${lemmaNameDstOrig//\'/\\\'}
echo lemmaNameDst = $lemmaNameDst

if [ $package_dst != $package_src ]; then
    echo "package_dst != package_src"
    find Lemma -type f -name "*.lean" -not -name "*.echo.lean" -print0 | xargs -0 grep -lZP "\b$lemmaNameSrc$submodule" | while IFS= read -r -d $'\0' file; do
        temp_file="${file}.tmp"
        awk -v package_src="$package_src" -v package_dst="$package_dst" '
        $1 == "open" {
            has_package_src = 0
            has_package_dst = 0
            for (i=2; i<=NF; i++) {
                if ($i == package_src) 
                    has_package_src = 1
                else if ($i == package_dst) 
                    has_package_dst = 1
            }
            if (has_package_src && !has_package_dst) {
                # Append package_dst to existing modules
                # $0 = $0 " " package_dst
                $(NF+1) = package_dst
            }
        }
        { print }
        ' "$file" > "$temp_file" && mv "$temp_file" "$file"
    done

    if [ $lemmaNameSrcOrig == $lemmaNameDstOrig ]; then
        echo "lemmaNameSrcOrig == lemmaNameDstOrig, no need to rename"
        exit
    fi
fi

# xargs: unmatched single quote; by default quotes are special to xargs unless you use the -0 option
find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -print0 | xargs -0 grep -lZE "open( [[:alnum:]_.]+)* $package_dst\b" | xargs -0 sed -i -E "s/([^.]\b|^)$lemmaNameSrc$submodule/\1$lemmaNameDst\2/g"