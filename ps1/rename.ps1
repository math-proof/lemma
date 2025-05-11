param(
    [string]$src,
    [string]$dst
)

. .\ps1\utility.ps1

# Normalize paths (assuming the normalize function converts to absolute paths)
$src = normalize $src
$dst = normalize $dst

Write-Host "src = $src"
Write-Host "dst = $dst"

# Construct source and destination file paths
$srcFile = "Lemma/" + ($src -replace '\.', '/') + ".lean"
$dstFile = "Lemma/" + ($dst -replace '\.', '/') + ".lean"

Write-Host "srcFile = $srcFile"
Write-Host "dstFile = $dstFile"

# Create parent directory for destination
$parent_path = Split-Path $dstFile -Parent
Write-Host "mkdir -p $parent_path"
New-Item -ItemType Directory -Path $parent_path -Force | Out-Null

# Check if destination file exists
if (Test-Path $dstFile) {
    Write-Error "error: $dstFile already exists"
    exit 1
}

# Check if source file exists
if (-not (Test-Path $srcFile)) {
    Write-Error "error: $srcFile does not exist"
    exit 1
}

# Move the file
Write-Host "mv $srcFile $dstFile"
Move-Item $srcFile $dstFile -Force

$srcReg = [regex]::Escape($src)
$submodule = '((\.[a-z]+)?(\b[^.]|$))'

# Replace all occurrences of the old namespace with the new one
Get-ChildItem -Path Lemma -Recurse -File -Filter *.lean | Where-Object { $_.Name -notlike "*.echo.lean" } | ForEach-Object {
    $content = [System.IO.File]::ReadAllText($_.FullName, [System.Text.Encoding]::UTF8)
    $newContent = $content -replace "$srcReg$submodule", "$dst`$1"
    if ($newContent -ne $content) {
        [System.IO.File]::WriteAllText($_.FullName, $newContent, [System.Text.UTF8Encoding]::new($false))
    }
}

$package_src = ($src -split '\.')[0]
$package_dst = ($dst -split '\.')[0]

$lemmaNameSrcOrig = if ($src.Contains('.')) { $src.Substring($src.IndexOf('.') + 1) } else { $src }
$lemmaNameDstOrig = if ($dst.Contains('.')) { $dst.Substring($dst.IndexOf('.') + 1) } else { $dst }

# Update 'open' statements if package changed
if ($package_dst -ne $package_src) {
    Get-ChildItem -Path Lemma -Recurse -File -Filter *.lean | Where-Object { $_.Name -notlike "*.echo.lean" } | ForEach-Object {
        $file = $_.FullName
        $tempFile = "$file.tmp"
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        $newContent = @()
        foreach ($line in $content) {
            if ($line -match '^open\s+') {
                $packages = $line -split '\s+' | Select-Object -Skip 1
                $hasPackageSrc = $packages -contains $package_src
                $hasPackageDst = $packages -contains $package_dst
                if ($hasPackageSrc -and !$hasPackageDst) {
                    $line += " $package_dst"
                }
            }
            $newContent += $line
        }
        [System.IO.File]::WriteAllText($tempFile, $newContent, [System.Text.UTF8Encoding]::new($false))
        Move-Item -Path $tempFile -Destination $file -Force
    }

    if ($lemmaNameSrcOrig -eq $lemmaNameDstOrig) {
        Write-Host "lemmaNameSrcOrig == lemmaNameDstOrig, no need to rename"
        exit
    }
}

# Final replacement for lemma names in files with the destination package
$lemmaNameSrc = [regex]::Escape($lemmaNameSrcOrig)

$filesWithOpenPackageDst = Get-ChildItem -Path Lemma -Recurse -File -Filter *.lean | Where-Object { 
    $_.Name -notlike "*.echo.lean" -and 
    (Select-String -Path $_.FullName -Pattern "open( [\w\.]+)* $package_dst\b" -Quiet)
}

$filesWithOpenPackageDst | ForEach-Object {
    $content = Get-Content $_.FullName -Raw -Encoding UTF8
    $newContent = $content -replace "\b$lemmaNameSrc$submodule", "$lemmaNameDstOrig`$1"
    if ($newContent -ne $content) {
        [System.IO.File]::WriteAllText($_.FullName, $newContent, [System.Text.UTF8Encoding]::new($false))
    }
}