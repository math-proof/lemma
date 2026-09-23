# conda install -c conda-forge jq
jq -r '.packages[] | "\(.url)\n\(.inputRev)\n\(.name)\n\(.rev)"' lake-manifest.json | while IFS= read -r url && IFS= read -r inputRev && IFS= read -r name && IFS= read -r rev; do
    if [ -d ".lake/packages/$name" ]; then
        # Get the current commit hash of the package
        current_rev=$(git -C ".lake/packages/$name" rev-parse HEAD 2>/dev/null)
        # Compare with the desired rev
        if [ "$current_rev" = "$rev" ]; then
            echo "Package $name is already at revision $rev. Skipping."
            continue
        fi
    else
        echo "fetch $name at $rev from $url by shallow cloning"
        mkdir -p ".lake/packages/$name"
        git -C ".lake/packages/$name" init
        git -C ".lake/packages/$name" remote add origin "$url"
    fi
    # The following command fetches only a limited number of commits from the history, which can significantly reduce the amount of data transferred.
    git -C ".lake/packages/$name" fetch --depth 1 origin "$rev"
    git -C ".lake/packages/$name" checkout "$rev"
done

lake clean
lake build
