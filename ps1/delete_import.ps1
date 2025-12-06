# rules: delete the import line if the file does not contain any of the specified patterns
$modules = @(
    'stdlib.Slice:Slice'
    'stdlib.List:\b(List|substr|slice|enumerate|is constant|swap)\b'
    'stdlib.SEq:≃'
    'sympy.core.relational:\n +denote '
    'sympy.core.logic:\n +mpr? \['
    'sympy.functions.elementary.integers:\b(is even|is odd|fract|sign|IntegerRing|SubSelf)\b|//'
    'sympy.tensor.tensor:\b(Tensor|Zeros|Ones|Indexed|Sliced)\b'
    'sympy.sets.sets:\b(Ioo|Ico|Iio|Icc|Iic|Ioc|Ici|Ioi|range)\b'
    'sympy.Basic:^([\s\S](?!\nimport Lemma))*$'
)

foreach ($entry in $modules) {
    # Split the entry into module and pattern
    $module, $pattern = $entry -split ':', 2
    # Escape dots in the module name for regex
    $escapedModule = $module -replace '\.', '\.'
    
    # Find files importing the module
    $files = Get-ChildItem -Path Lemma -Recurse -Include '*.lean' -Exclude '*.echo.lean' |
        Where-Object { !$_.PSIsContainer } |
        Where-Object {
            Select-String -Path $_.FullName -Pattern "^import $escapedModule`$" -CaseSensitive -Quiet
        }

    # Process each file
    foreach ($file in $files) {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        if ($content -match $pattern) { continue }
        # deal with files that don't contain the pattern
        Write-Host "Processing file: $($file.FullName)"

        # Find matching import lines
        $matchingLines = [regex]::Matches($content, "^import $escapedModule`$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
        
        if ($matchingLines.Count -gt 0) {
            Write-Host "The following line(s) will be removed:"
            $matchingLines | ForEach-Object {
                Write-Host "$($file.FullName): $($_.Value)"
            }

            # Remove the import lines and save the file without BOM
            $newContent = [regex]::Replace($content, "^import $escapedModule`$\r?\n?", '', [System.Text.RegularExpressions.RegexOptions]::Multiline)
            [System.IO.File]::WriteAllText($file.FullName, $newContent, [System.Text.UTF8Encoding]::new($false))
        }
    }
}
