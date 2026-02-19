# List of package names to process
packages=$(find Lemma -mindepth 1 -maxdepth 1 -type d -printf '%f\n')
# Loop over each package
for package in $packages; do
    # Find files meeting the criteria for the current package
    grep -rlZ --include='*.lean' --exclude='*.echo.lean' -P "open ([[:alnum:]_]+ )*$package\b(?! [(])" Lemma | xargs -0 grep -LZ "import Lemma\.$package\." \
    | while IFS= read -r -d $'\0' file; do
        echo "Processing file: $file"
        echo "The following lines will be modified (removing '$package' from 'open' statements):"
        grep -nE "open ([[:alnum:]_]+ )*$package\b" "$file"
        sed -i -E "
          /^open / {
            # Remove all occurrences of the current package word
            s/\b$package\b//g
            # Collapse multiple spaces to one
            s/  +/ /g
            # Trim trailing space
            s/ $//
            # Delete the line if it now reads exactly 'open'
            /^open$/d
          }
        " "$file"
    done
done