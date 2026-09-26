# usage:
# .\ps1\setup.ps1 [-clean] [-version vX.Y.Z]
param(
    [switch]$clean,
    [String]$version = "v4.33.1"
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
            Pop-Location
            throw "Failed to download Lean $version from $url. Error: $_"
        }
    }
    # mkdir $targetDir
    New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
    tar --strip-components=1 -xf $tarFile -C $targetDir
    # delete $tarFile
    Remove-Item $tarFile -Force
    Write-Host "✅ Lean $version installed successfully."
    $systemprofile = "C:\Windows\System32\config\systemprofile\.elan\toolchains"
    # copy the entire folder $targetDir to $systemprofile
    # if the destination folder already exists, skip copying
    if (Test-Path "$systemprofile\$targetDir\bin\lean.exe") {
        Write-Host "Lean $version already exists in systemprofile, skipping copying."
    }
    else {
        Write-Host "Copying $targetDir to systemprofile..."
        Copy-Item -Path "$targetDir" -Destination "$systemprofile" -Recurse -Force
    }
}
Pop-Location
$toolchain = "leanprover/lean4:$version"
elan default $toolchain
elan override set $toolchain
elan override unset --nonexistent
Write-Host "✅ elan default and directory override set to $toolchain"

[Console]::OutputEncoding = [Text.Encoding]::UTF8
$OutputEncoding = [Text.Encoding]::UTF8

$content = Get-Content "lean-toolchain" -Raw
$versionRegex = "leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?)"
# Use regex to extract the version (the part starting with v...)
if ($content -match $versionRegex) {
    if ($matches[1] -eq $version) {
        $needsClean = $false
        Write-Host "leanprover/lean4:$version is already installed, skipping"
    }
    else {
        $needsClean = $true
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
    git -C $packagePath checkout --force $version
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
    $url = $package.url

    # Check if the package directory exists
    if (Test-Path $packagePath) {
        # Get the current commit hash of the package
        $current_rev = & git -C $packagePath rev-parse HEAD 2>$null
        # Compare with the desired rev
        if ($current_rev -eq $rev) {
            Write-Host "Package $name is already at revision $rev. Skipping fetch."
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
    git -C $packagePath checkout --force $rev
}

# Save updated manifest
if ($updated) {
    $jsonString = $currentManifest | ConvertTo-Json -Depth 10
    [IO.File]::WriteAllText("lake-manifest.json", $jsonString, [Text.UTF8Encoding]::new($false))
    Write-Host "🌟 lake-manifest.json updated successfully."
}

$currentManifest = Get-Content -Raw -Path "lake-manifest.json" | ConvertFrom-Json
foreach ($package in $currentManifest.packages) {
    $name = $package.name
    $rev = $package.rev
    $packagePath = ".lake/packages/$name"
    if (-Not (Test-Path $packagePath)) {
        Write-Host "warning: package $name missing at $packagePath; skip clean reset"
        continue
    }
    Write-Host "🧹 reset package $name to clean manifest rev $rev"
    git -C $packagePath cat-file -e "${rev}^{commit}" 2>$null
    if ($LASTEXITCODE -ne 0) {
        git -C $packagePath fetch --depth 1 origin $rev
        if ($LASTEXITCODE -ne 0) {
            throw "Git fetch failed for $name with exit code $LASTEXITCODE"
        }
    }
    git -C $packagePath checkout --force $rev
    if ($LASTEXITCODE -ne 0) {
        throw "Git checkout failed for $name with exit code $LASTEXITCODE"
    }
    git -C $packagePath reset --hard HEAD
    git -C $packagePath clean -fd
}

# Run lake commands
$start = Get-Date
if ($needsClean -or $clean) {
    Write-Host "Lean toolchain changed recently — running lake clean"
    lake clean
}
# Mathlib oleans come from the cache.
Write-Host "⏳ lake exe cache get..."
lake exe cache get
if ($LASTEXITCODE -ne 0) {
    throw "lake exe cache get failed with exit code $LASTEXITCODE"
}

# Ensure Node.js (needed to build ProofWidgets widget JS).
# make sure node is available https://nodejs.org/en/download
$node = Get-Command node -ErrorAction SilentlyContinue
if ($null -ne $node) {
    Write-Host "✅ Node.js is already installed. Version: $(node -v)"
} else {
    $installDir = "D:\Program Files\nodejs"
    Write-Host "⚠️ Node.js not found. Installing v22.20.0 to $installDir ..."
    $nodeInstaller = "$env:TEMP\node-lts.msi"
    Invoke-WebRequest -Uri "https://nodejs.org/dist/v22.20.0/node-v22.20.0-x64.msi" -OutFile $nodeInstaller
    $proc = Start-Process msiexec.exe -Wait -PassThru -ArgumentList "/i `"$nodeInstaller`" INSTALLDIR=`"$installDir`" /quiet /norestart"
    Remove-Item $nodeInstaller -Force
    if ($proc.ExitCode -ne 0) {
        throw "Node.js MSI install failed with exit code $($proc.ExitCode)"
    }
    # Refresh PATH for this session (machine + user) and include installDir.
    $env:Path = [Environment]::GetEnvironmentVariable("Path", "Machine") + ";" + [Environment]::GetEnvironmentVariable("Path", "User")
    if ($env:Path -notlike "*$installDir*") {
        $env:Path = "$installDir;$env:Path"
    }
    if ($null -eq (Get-Command node -ErrorAction SilentlyContinue)) {
        throw "Node.js installed but node is still not on PATH"
    }
    Write-Host "✅ Node.js installation complete. Version: $(node -v)"
}

# Build ProofWidgets (incl. widget JS) directly inside the package.
$packagePath = ".lake/packages/proofwidgets"
if (-Not (Test-Path $packagePath)) {
    throw "$packagePath not found"
}
Write-Host "⏳ build package proofwidgets (Node)..."
Push-Location $packagePath
lake build
$pwExit = $LASTEXITCODE
Pop-Location
if ($pwExit -ne 0) {
    throw "lake build in $packagePath failed with exit code $pwExit"
}

# now build the entire project
Write-Host "⏳ building the entire project..."
lake build
# build specifically sympy.printing.echo for latex printing support
lake build sympy.printing.echo
$end = Get-Date
$totalTime = ($end - $start).TotalSeconds
Write-Host "🏁 Build completed in $totalTime seconds." -ForegroundColor Cyan
.\ps1\run.ps1
