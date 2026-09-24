<#
.SYNOPSIS
  Remove `open <Package>` statements for packages not imported in a Lean file.
  If a .lean file path is given as argument, process only that file.
  Otherwise, scan all files under Lemma/ as before.

.PARAMETER FilePath
  Path to a single .lean file to process. Optional.

.EXAMPLE
  .\delete_open.ps1 Lemma\Real\SomeLemma.lean
  .\delete_open.ps1
#>
param(
  [Parameter(Position = 0)]
  [string]$FilePath
)

$packages = Get-ChildItem -Path "Lemma" -Directory | Select-Object -ExpandProperty Name

if ($FilePath) {
  $resolved = (Resolve-Path $FilePath).Path
  $filesToScan = Get-ChildItem -Path $resolved -Include '*.lean' -File
} else {
  $filesToScan = Get-ChildItem -Path Lemma -Recurse -Include '*.lean' -Exclude '*.echo.lean'
}

foreach ($package in $packages) {
  $escapedPackage = [regex]::Escape($package)
  $patternOpen = "open(?! scoped\b) ([\w]+ )*$escapedPackage\b(?! [(])"
  $importPattern = "import Lemma\.$escapedPackage\."

  $filesWithOpen = $filesToScan | Where-Object {
    (Select-String -Path $_.FullName -Pattern $patternOpen -Quiet)
  }

  $filesToProcess = $filesWithOpen | Where-Object {
    -not (Select-String -Path $_.FullName -Pattern $importPattern -Quiet)
  }

  foreach ($file in $filesToProcess) {
    $content = Get-Content $file.FullName -Encoding UTF8
    $newContent = @()
    $newContent = foreach ($line in $content) {
      if ($line -match $patternOpen) {
        $newLine = $line -replace "\b$escapedPackage\b", ''
        $newLine = $newLine -replace ' +', ' '
        $newLine = $newLine.TrimEnd()
        if ($newLine -eq 'open') { continue }
        if ($newLine -ne $line) {
          Write-Host "in $($file.FullName), removing '$package' from 'open' statements: $line"
        }
        $newLine
      } else {
        $line
      }
    }
    $newContent = $newContent -join "`n"
    $newContent += "`n"
    [System.IO.File]::WriteAllText($file.FullName, $newContent, [System.Text.UTF8Encoding]::new($false))
  }
}
