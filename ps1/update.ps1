# usage:
# . .\ps1\update.ps1
# Read the lean-toolchain file
param(
    [String]$version = "v4.24.0"
)
$versionNumber = $version.Substring(1)
# cd ~/.elan/toolchains
Push-Location "$HOME\.elan\toolchains"
$targetDir = "leanprover--lean4---$version"
# check if $targetDir already exists
if (Test-Path "$targetDir\bin\lean.exe") {
    Write-Host "Lean $version is already installed, skipping installing."
}
else {
    $tarFile = "lean-$versionNumber-windows.tar.zst"
    # check if $tarFile exists
    if (-Not (Test-Path $tarFile)) {
        $url = "https://releases.lean-lang.org/lean4/$version/$tarFile"
        # download from $url and save to ~/.elan/toolchains
        Write-Host "Downloading Lean $version from $url..."
        try {
            Invoke-WebRequest -Uri $url -OutFile $tarFile
            if ($LASTEXITCODE -ne 0) {
                throw "Download failed with exit code $LASTEXITCODE"
            }
        }
        catch {
            throw "Failed to download Lean $version from $url. Error: $_"
        }
    }
    # mkdir $targetDir
    New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
    tar --strip-components=1 -xf $tarFile -C $targetDir
    # delete $tarFile
    Remove-Item $tarFile -Force
    Write-Host "✅ Lean $version installed successfully."
    # copy the entire folder $targetDir to C:\Windows\System32\config\systemprofile\.elan\toolchains
    # if the destination folder already exists, skip copying
    if (Test-Path "C:\Windows\System32\config\systemprofile\.elan\toolchains\$targetDir\bin\lean.exe") {
        Write-Host "Lean $version already exists in systemprofile, skipping copying."
    }
    else {
        Write-Host "Copying Lean $version to systemprofile..."
        Copy-Item -Path "$targetDir" -Destination "C:\Windows\System32\config\systemprofile\.elan\toolchains\" -Recurse -Force
    }
}
Pop-Location
elan override set leanprover/lean4:$versionNumber

[Console]::OutputEncoding = [Text.Encoding]::UTF8
$OutputEncoding = [Text.Encoding]::UTF8

$content = Get-Content "lean-toolchain" -Raw
$versionRegex = "leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?)"
# Use regex to extract the version (the part starting with v...)
if ($content -match $versionRegex) {
    if ($matches[1] -eq $version) {
        Write-Host "leanprover/lean4:$version is already installed, skipping"
    }
    else {
        # write the text `leanprover/lean4:$version` into file lean-toolchain, without BOM
        $newContent = "leanprover/lean4:$version`n"
        # Write to file without BOM
        [IO.File]::WriteAllText("lean-toolchain", $newContent, [Text.UTF8Encoding]::new($false))
        Write-Host "✅ lean-toolchain updated to $newContent"
    }
}
else {
    throw "Could not find version info in lean-toolchain"
}
$name="mathlib"
$packagePath = ".lake/packages/$name"

# Read lean-toolchain of mathlib
$toolchainFile = Join-Path $packagePath "lean-toolchain"
if (-Not (Test-Path $toolchainFile)) {
    Write-Error "lean-toolchain file not found in $packagePath"
    exit 1
}

$content = Get-Content $toolchainFile -Raw
if ($content -match $versionRegex) {
    $mathlibVersion = $matches[1]
} else {
    Write-Error "Could not extract Lean version from mathlib lean-toolchain"
    exit 1
}

if ($mathlibVersion -eq $version) {
    Write-Host "✅ mathlib already matches Lean version $version. Skipping."
}
else {
    Write-Host "⏳ Checking out mathlib tag $version (current: $mathlibVersion)..."
    git -C $packagePath fetch --depth 1 origin tag $version
    if ($LASTEXITCODE -ne 0) {
        throw "Git fetch failed with exit code $LASTEXITCODE"
    }
    git -C $packagePath checkout $version
}

$manifestFile = Join-Path $packagePath "lake-manifest.json"
if (-Not (Test-Path $manifestFile)) {
    Write-Error "lake-manifest.json not found in $packagePath"
    exit 1
}
$mathlibManifest = Get-Content -Raw -Path $manifestFile | ConvertFrom-Json
$rev = & git -C $packagePath rev-parse HEAD 2>$null
$mathlibManifest.packages += [PSCustomObject]@{
    name = $name
    inputRev = "master"
    rev = $rev
}

$updated = $false
$currentManifest = Get-Content -Raw -Path "lake-manifest.json" | ConvertFrom-Json
foreach ($package in $mathlibManifest.packages) {
    $name = $package.name
    Write-Host "updating $name in lake-manifest.json from mathlib"
    $inputRev = $package.inputRev
    $rev = $package.rev
    ## how to update $currentManifest if the corresponding field (inputRev/rev) has been changed?
    # Find corresponding package in current manifest
    $currentPackage = $currentManifest.packages | Where-Object { $_.name -eq $name }
    if ($null -eq $currentPackage) {
        Write-Host "➕ Package $name not found in current manifest, adding it."
        # Append the new package
        $currentManifest.packages += $package
        $updated = $true
    }
    else {
        # Check if inputRev or rev differs
        if ($currentPackage.inputRev -ne $inputRev) {
            $currentPackage.inputRev = $inputRev
            Write-Host "✅ Updated $name : inputRev=$inputRev"
            $updated = $true
        }
        if ($currentPackage.rev -ne $rev) {
            $currentPackage.rev = $rev
            Write-Host "✅ Updated $name : rev=$rev"
            $updated = $true
        }
    }

    $packagePath = ".lake/packages/$name"

    # Check if the package directory exists
    if (Test-Path $packagePath) {
        # Get the current commit hash of the package
        $current_rev = & git -C $packagePath rev-parse HEAD 2>$null
        # Compare with the desired rev
        if ($current_rev -eq $rev) {
            Write-Host "Package $name is already at revision $rev. Skipping."
            continue
        }
    } else {
        Write-Host "fetch $name at $rev from $url by shallow cloning"
        New-Item -ItemType Directory -Path $packagePath -Force | Out-Null
        git -C $packagePath init | Out-Null
        git -C $packagePath remote add origin $url
    }
    
    # Fetch only a limited number of commits from the history
    git -C $packagePath fetch --depth 1 origin $rev
    if ($LASTEXITCODE -ne 0) {
        throw "Git fetch failed with exit code $LASTEXITCODE"
    }
    git -C $packagePath checkout $rev
}

# Save updated manifest
if ($updated) {
    $jsonString = $currentManifest | ConvertTo-Json -Depth 10
    [IO.File]::WriteAllText("lake-manifest.json", $jsonString, [Text.UTF8Encoding]::new($false))
    Write-Host "🌟 lake-manifest.json updated successfully."
}

# Check if Node.js is installed
$node = Get-Command node -ErrorAction SilentlyContinue
# make sure node is available https://nodejs.org/en/download
if ($null -ne $node) {
    Write-Host "✅ Node.js is already installed. Version: $(node -v)"
} else {
    $installDir = "D:\Program Files\nodejs"

    Write-Host "⚠️ Node.js not found. Installing latest LTS version..."

    # Download latest Node.js LTS installer (x64 .msi)
    $nodeInstaller = "$env:TEMP\node-lts.msi"
    Invoke-WebRequest -Uri "https://nodejs.org/dist/v22.20.0/node-v22.20.0-x64.msi" -OutFile $nodeInstaller

    # Install silently
    Start-Process msiexec.exe -Wait -ArgumentList "/i `"$nodeInstaller`" INSTALLDIR=`"$installDir`" /quiet /norestart"

    # Clean up installer
    Remove-Item $nodeInstaller -Force

    Write-Host "✅ Node.js installation complete. Version: $(node -v)"
}

# Run lake commands
$start = Get-Date
lake clean
# lake build -v
lake build
$end = Get-Date
$totalTime = ($end - $start).TotalSeconds
Write-Host "🏁 Build completed in $totalTime seconds." -ForegroundColor Cyan
. .\ps1\run.ps1