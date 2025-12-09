# List of package names to process
$packages = Get-ChildItem -Path "Lemma" -Directory | Select-Object -ExpandProperty Name

# Loop over each package
foreach ($package in $packages) {
    $escapedPackage = [regex]::Escape($package)
    $patternOpen = "open ([\w]+ )*$escapedPackage\b(?! [(])"
    $importPattern = "import Lemma\.$escapedPackage\."

    # Find files with open statement but without import
    $filesWithOpen = Get-ChildItem -Path Lemma -Recurse -Include '*.lean' -Exclude '*.echo.lean' | Where-Object {
        (Select-String -Path $_.FullName -Pattern $patternOpen -Quiet)
    }
    
    $filesToProcess = $filesWithOpen | Where-Object {
        -not (Select-String -Path $_.FullName -Pattern $importPattern -Quiet)
    }

    # Process each file
    foreach ($file in $filesToProcess) {
        # Show lines to be modified
        $content = Get-Content $file.FullName -Encoding UTF8
        $newContent = @()
        # Modify file content
        $newContent = foreach ($line in $content) {
            if ($line -match '^open ') {
                # Remove package name
                $newLine = $line -replace "\b$escapedPackage\b", ''
                # Collapse spaces
                $newLine = $newLine -replace ' +', ' '
                # Trim trailing space
                $newLine = $newLine.TrimEnd()
                # Skip empty 'open' lines
                if ($newLine -eq 'open') { continue }
                Write-Host "in $($file.FullName), removing '$package' from 'open' statements: $line"
                $newLine
            } else {
                $line
            }
        }
        $newContent = $newContent -join "`n"
        $newContent += "`n"
        # Write changes back to file
        [System.IO.File]::WriteAllText($file.FullName, $newContent, [System.Text.UTF8Encoding]::new($false))
    }
}