$modules = @(
    'sympy.core.relational:^ +denote '
    'sympy.core.logic:^ +mpr? \['
    'sympy.functions.elementary.integers:\b(is even|is odd|fract|sign|IntegerRing)\b|//'
    'sympy.tensor.tensor:\b(Tensor|Zeros|Ones|Indexed|Sliced)\b'
    'sympy.sets.sets:\b(Ioo|Ico|Iio|Icc|Iic|Ioc|Ici|Ioi|range)\b'
    'stdlib.Slice:Slice'
    'stdlib.List:\b(List|substr|slice|enumerate|is constant|swap)\b'
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

    # Filter files that don't contain the pattern
    $filesToProcess = $files | Where-Object {
        -not (Select-String -Path $_.FullName -Pattern $pattern -CaseSensitive -Quiet)
    }

    # Process each file
    foreach ($file in $filesToProcess) {
        Write-Host "Processing file: $($file.FullName)"
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        
        # Find matching import lines
        $matchingLines = [regex]::Matches($content, "^import $escapedModule`$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
        
        if ($matchingLines.Count -gt 0) {
            Write-Host "The following line(s) will be removed:"
            $matchingLines | ForEach-Object {
                Write-Host "$($file.Name): $($_.Value)"
            }
            
            # Remove the import lines and save the file without BOM
            $newContent = [regex]::Replace($content, "^import $escapedModule`$\r?\n?", '', [System.Text.RegularExpressions.RegexOptions]::Multiline)
            [System.IO.File]::WriteAllText($file.FullName, $newContent, [System.Text.UTF8Encoding]::new($false))
        }
    }
}
