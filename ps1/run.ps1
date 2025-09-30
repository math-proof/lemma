# usage :
# . ps1\run.ps1
param(
    [int]$limit = 4096
)
[System.Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$OutputEncoding = [System.Text.Encoding]::UTF8
$start_time = [DateTimeOffset]::Now.ToUnixTimeSeconds()
. .\ps1\utility.ps1

$__file__ = $MyInvocation.MyCommand.Path | Resolve-Path
$root = Split-Path -Path $__file__ -Parent | Split-Path -Parent
$user = $root | Split-Path -Leaf
Write-Host "user = $user"

Set-Content -Path test.lean -Value $null

$imports_dict = @{}

function echo_import {
    param(
        [string]$file
    )
    $file = $file.Substring($root.Length + 1)
    $lemma = Join-Path (Split-Path $file -Parent) ([System.IO.Path]::GetFileNameWithoutExtension($file))
    $module = $lemma -replace '\\', '.'
    Add-Content -Path test.lean -Value "import $module"
    
    $module = $module -creplace '^Lemma\.', ''
    $lines = @(Get-Content -Path $file | Where-Object { $_ -match '^import\s+' } | ForEach-Object { $_ -replace '^import\s+', '' })
    
    if ($lines.Count -eq 0) {
        $imports_dict[$module] = "[]"
    } else {
        $imports_dict[$module] = $lines | ConvertTo-Json -Compress
    }
}

Get-ChildItem -Path "Lemma" -Recurse -File -Filter "*.lean" |
Where-Object { $_.Name -notlike "*.echo.lean" } |
ForEach-Object {
    echo_import $_.FullName
}

# Read the contents of test.lean into $imports
$imports = Get-Content test.lean

# Create or clear test.log
New-Item -Path test.log -ItemType File -Force

# Split into batches
$batches = batches -Data $imports -BatchSize $limit

# Write each batch to a separate file
for ($i = 0; $i -lt $batches.Count; $i++) {
    $batches[$i] | Set-Content "test.$i.lean"
    if ($limit -eq 1) {
        $batchContent = $batches[$i] -join " "
        Write-Host "executing: $batchContent" -ForegroundColor Green
    }
    cmd /c "lake setup-file test.$i.lean" 2>&1 | Select-Object -SkipLast 1 | Tee-Object -FilePath test.log -Append
    # Start-Sleep -Seconds 1
}

# Remove lines starting with 'import ' from test.lean
(Get-Content test.lean) | ForEach-Object { $_ -creplace '^import ', '' } | Set-Content test.lean

# Read the modified content into $imports again
$imports = Get-Content test.lean

# Clear the contents of test.lean
Set-Content test.lean -Value $null

# Output "modules:"
Write-Output "modules:"

# Create or clear the test.sql file with the initial INSERT statement
"INSERT INTO lemma (user, module, imports, open, def, lemma, error, date) VALUES " | Out-File -FilePath test.sql -Encoding utf8

# Process each module in the imports array
foreach ($module in $imports) {
    # Remove the 'Lemma.' prefix from the module name
    $module = $module -creplace '^Lemma\.', ''

    # Skip processing if the module is not present in imports_dict or has an empty value
    if (-not $imports_dict.ContainsKey($module) -or [string]::IsNullOrEmpty($imports_dict[$module])) {
        Write-Output "imports_dict[$module] = $($imports_dict[$module])"
        continue
    }
    $submodules = $imports_dict[$module]
    $submodules = $submodules -replace "'", "''"
    "  ('$user', `"$module`", '$submodules', '[]', '[]', '[]', '[]', '[]')," | Add-Content -Path test.sql
}

# Get all .lean files except *.echo.lean under Lemma/
Get-ChildItem -Recurse -Path "Lemma" -Include *.lean -Exclude *.echo.lean | ForEach-Object {
    $file = $_.FullName
    if (!(Select-String -Path $file -Pattern '^@\[main, [^]]+\]' -Quiet)) {return}
    $file = Resolve-Path -Relative $file
    $module = $file -creplace '^\.\\Lemma\\', ''
    $module = $module -replace '\\', '.'
    $module = $module -replace '\.lean$', ''

    if (Select-String -Path $file -Pattern '^@\[main, .*\b(?<!mpr?\.)comm( [0-9]+)?\b' -Quiet) {
        $tokens = $module -split '\.'
        $match = Select-String -Path $file -Pattern '^@\[main, .*\b(?<!mpr?\.)comm( [0-9]+)?\b' -AllMatches
        if ($match) {
            # Take the first match's first group
            $deBruijn = $match.Matches[0].Groups[1].Value
        }
        switch -regex ($tokens[2]) {
            "^(eq|is|as|ne)$" {
                $tmp = $tokens[1]
                $tokens[1] = $tokens[3]
                $tokens[3] = $tmp
            }
            default {
                $first = $tokens[1]
                if ($first -like 'Eq_*') {
                    $first = "Eq" + $first.Substring(3)
                } elseif ($first -like 'Eq*') {
                    $first = "Eq_" + $first.Substring(2)
                } elseif ($first -like 'SEq_*') {
                    $first = "SEq" + $first.Substring(4)
                } elseif ($first -like 'SEq*') {
                    $first = "SEq_" + $first.Substring(3)
                } else {
                    Write-Host "panic! Expected the operator to be 'S?Eq.*', got: $first in $module"
                }
                $tokens[1] = $first
            }
        }
        $new_module = $tokens -join "."
        Add-Content -Path "test.sql" -Value "  ('$user', ""$new_module"", '[]', '[]', '[]', '[]', '[]', '[]'),"
    }
    if (Select-String -Path $file -Pattern '^@\[main, .*\bmp\b' -Quiet) {
        if ($module -match '^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+)(\.of\..+)?$') {
            $new_module = "$($matches[1]).$($matches[3]).of.$($matches[2])$($matches[4])"
            Add-Content -Path "test.sql" -Value "  ('$user', ""$new_module"", '[]', '[]', '[]', '[]', '[]', '[]'),"
        }
    }
    if (Select-String -Path $file -Pattern '^@\[main, .*\bmpr\b' -Quiet) {
        if ($module -match '^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+)(\.of\..+)?$') {
            $new_module = "$($matches[1]).$($matches[2]).of.$($matches[3])$($matches[4])"
            Add-Content -Path "test.sql" -Value "  ('$user', ""$new_module"", '[]', '[]', '[]', '[]', '[]', '[]'),"
        }
    }
    if (Select-String -Path $file -Pattern '^@\[main, .*\bmp\.comm\b' -Quiet) {
        $tokens = $module -split '\.'
        Write-Host "@[mp.comm] at $file"
    }
    if (Select-String -Path $file -Pattern '^@\[main, .*\bmpr\.comm\b' -Quiet) {
        $tokens = $module -split '\.'
        Write-Host "@[mpr.comm] at $file"
    }
}

# Modify the last line to complete the SQL statement
$content = Get-Content -Path test.sql
if ($content.Count -gt 0) {
    $content[-1] = $content[-1] -replace ',$', ''
    $content += "ON DUPLICATE KEY UPDATE imports = VALUES(imports), error = VALUES(error);"
    $content | Set-Content -Path test.sql
}

Write-Output "plausible:"

# Extract and process the modules with 'sorry' warnings
$cwd = [regex]::Escape((Get-Location).Path) 
$cwd = "($cwd\\|(\.[\\/])*)"
$sorryModules = Get-Content test.log | 
    Select-String -Pattern "^warning: $cwd[\w\\/]+\.lean:\d+:\d+: declaration uses 'sorry'" | 
    ForEach-Object {
        $_.Line -replace "^warning: $cwd", '' -replace '\.lean:\d+:\d+: declaration uses ''sorry''', '' -replace '[\\/]', '.'
    } | 
    Select-Object -Unique

foreach ($module in $sorryModules) {
    # Output the .lean file path with slashes
    ($module -replace '\.', '/') + ".lean" | Write-Output
    
    # Remove 'Lemma.' prefix from module name
    $module = $module -creplace '^Lemma\.', ''

    # Skip modules starting with 'sympy'
    if ($module -match '^sympy') {
        continue
    }
    
    # Generate SQL statement and append to test.sql
    $sqlLine = @"
UPDATE lemma set error = '[{"code": "", "file": "", "info": "declaration uses ''sorry''", "line": 0, "type": "warning"}]' where user = '$user' and module = "$module";
"@
    Add-Content -Path test.sql -Value $sqlLine
}

Write-Output "failed:"

# Read test.log and extract failing modules
$content = Get-Content test.log
$flag = $false
$failingModules = @()
foreach ($line in $content) {
    if ($line -match 'Some required targets logged failures:') {
        $flag = $true
        continue
    }
    if ($flag) {
        if ($line -notmatch '^- ') {
            $flag = $false
        }
        else {
            $module = $line -replace '^- ', ''
            $failingModules += $module
        }
    }
}

$failingModules = $failingModules | Select-Object -Unique
# Process each failing module
foreach ($module in $failingModules) {
    # Output transformed module path
    $leanPath = $module -replace '\.', '/'
    Write-Output "$leanPath.lean"

    # Remove 'Lemma.' prefix
    $modifiedModule = $module -creplace '^Lemma\.', ''

    # Skip modules starting with sympy
    if ($modifiedModule -like "sympy*") {
        continue
    }

    # Generate SQL statement
    $sql = @"
UPDATE lemma set error = '[{"code": "", "file": "", "info": "", "line": 0, "type": "error"}]' where user = '$user' and module = "$modifiedModule";
"@
    
    # Append to SQL file
    $sql | Add-Content -Path test.sql -Encoding UTF8
}

if (-not $env:MYSQL_PORT) {
    $env:MYSQL_PORT = 3306 
}
# Create a temporary config file with .ini extension
$tempConfigPath = [System.IO.Path]::ChangeExtension((New-TemporaryFile).FullName, '.ini')
@"
[client]
user = $env:MYSQL_USER
password = $env:MYSQL_PASSWORD
port = $env:MYSQL_PORT
"@ | Set-Content $tempConfigPath

# Run the initial MySQL command and log output

mysql --defaults-extra-file="$tempConfigPath" -D axiom -e "update lemma set error = NULL" 2>&1 | Tee-Object -FilePath test.log

# Check for database existence error
if (Select-String -Path test.log -Pattern "ERROR \d+ \(\d+\): Unknown database 'axiom'") {
    Write-Output "CREATE DATABASE axiom;"
    
    # Create the database
    mysql --defaults-extra-file="$tempConfigPath" -e "CREATE DATABASE axiom;"
    # mysql "-u$env:MYSQL_USER" "-p$env:MYSQL_PASSWORD" "-P$env:MYSQL_PORT" -e "CREATE DATABASE axiom;"
    
    # Check if database creation was successful
    if ($LASTEXITCODE -eq 0) {
        Write-Output "Database 'axiom' created successfully."
        
        # Re-run the script with original arguments
        & $MyInvocation.MyCommand.Path @args
        
        exit 0
    } else {
        Write-Output "Failed to create database 'axiom'."
        exit 1
    }
}

# Run the MySQL command and log output

Get-Content test.sql | mysql --defaults-extra-file="$tempConfigPath" -D axiom 2>&1 | Tee-Object -FilePath test.log

# Check for specific error pattern
if (Select-String -Path test.log -Pattern "ERROR \d+ \(\w+\) at line \d+: Table 'axiom.lemma' doesn't exist" -Quiet) {
    # Create the table
    Get-Content sql/create/lemma.sql | mysql --defaults-extra-file="$tempConfigPath" -D axiom
    # Get-Content sql/create/lemma.sql | mysql "-u$env:MYSQL_USER" "-p$env:MYSQL_PASSWORD" "-P$env:MYSQL_PORT" -D axiom
    if ($?) {
        Write-Host "Table 'lemma' created successfully."
        .\ps1\run.ps1
        exit 0
    } else {
        Write-Host "Failed to create table 'lemma'."
        exit 1
    }
}

# Execute MySQL command and log output
mysql --defaults-extra-file="$tempConfigPath" -D axiom -e "delete from lemma where error is NULL" 2>&1 | Tee-Object -FilePath test.log

# Calculate time cost
$end_time = [System.DateTimeOffset]::Now.ToUnixTimeSeconds()
$time_cost = $end_time - $start_time

# Output the time cost (optional)
Write-Output "Operation completed in $time_cost seconds"

function remove_invalid_ir_file {
    param(
        [Parameter(Mandatory=$true, ValueFromPipeline=$true)]
        [System.IO.FileInfo]$File
    )

    $module = ($File | Resolve-Path -Relative) -replace '\\', '/'
    
    # Extract module path after third directory
    if ($module -match '^(?:[^/]*/){3}(.*)') {
        $module = $Matches[1]
    } else {
        Write-Host "Invalid path format: $module"
        return
    }

    # Remove extension and append .lean
    $module = ($module -split '\.')[0]
    $module = "$module.lean"

    # Check if corresponding .lean file exists
    if (-not (Test-Path -Path $module -PathType Leaf)) {
        Write-Host "rm $($File.FullName), since $module doesn't exist"
        Remove-Item -Path $File.FullName -Force
    }
}

# Find and process target files
Get-ChildItem -Path .lake\build\ir -Recurse -File |
    Where-Object { $_.Extension -match '^\.(trace|olean|ilean|hash|c)$' } |
    ForEach-Object { remove_invalid_ir_file -File $_ }

function remove_invalid_lib_file {
    param(
        [Parameter(ValueFromPipeline=$true)]
        [string]$File
    )
    process {
        # Convert to relative path and normalize slashes
        $relativePath = ($File | Resolve-Path -Relative) -replace '\\', '/'
        
        # Remove first four directory components
        $modulePart = $relativePath -replace '^([^/]*/){4}', ''
        
        # Remove all extensions and append .lean
        $module = $modulePart -replace '^([^.]*)\..*$', '$1.lean'
        
        # Check if the target .lean file exists
        if (-not (Test-Path -Path $module -PathType Leaf)) {
            Write-Host "rm $File, since $module doesn't exist"
            Remove-Item -Path $File
        }
    }
}

# Find and process files
Get-ChildItem -Path .lake\build\lib -Recurse -File |
    Where-Object { $_.Extension -match '\.(trace|olean|ilean|hash|c)$' } |
    ForEach-Object { $_.FullName } |
    remove_invalid_lib_file

function remove_invalid_echo_file {
    param(
        [string]$file
    )
    $fileItem = Get-Item $file
    $dir = $fileItem.Directory.FullName
    $fileName = $fileItem.Name
    $moduleBase = ($fileName -split '\.', 2)[0]  # Split at first dot
    $moduleName = "$moduleBase.lean"
    $modulePath = Join-Path -Path $dir -ChildPath $moduleName
    if (-not (Test-Path -Path $modulePath -PathType Leaf)) {
        Write-Host "rm $file, because $modulePath does not exist"
        Remove-Item -Path $file
    }
}

# Process .echo.lean files under Lemma
Get-ChildItem -Path Lemma -Recurse -File | 
    Where-Object { $_.Name -match '\.echo\.lean$' } | 
    ForEach-Object { remove_invalid_echo_file -file $_.FullName }

# Remove empty directories (current directory and .lake/build)
@('.', '.lake/build') | ForEach-Object {
    $path = $_
    Get-ChildItem -Path $path -Directory -Recurse | 
        Where-Object { 
            -not (Get-ChildItem -LiteralPath $_.FullName -Force | Select-Object -First 1)
        } | 
        Sort-Object -Property FullName -Descending | 
        ForEach-Object {
            Remove-Item -Path $_.FullName -Force
        }
}

Write-Output "seconds cost    = $time_cost"
Write-Output "total theorems  = $($imports.Count)"
Write-Output "total plausible = $($sorryModules.Count)"
Write-Output "total failed    = $($failingModules.Count)"

# Execute the delete_open.ps1 script located in the ps1 directory
.\ps1\delete_open.ps1

# Execute the delete_import.ps1 script located in the ps1 directory
.\ps1\delete_import.ps1

Remove-Item $tempConfigPath -Force -ErrorAction SilentlyContinue

# Find all .lean files (excluding *.echo.lean) that import both sympy.Basic and Lemma.*
Get-ChildItem -Recurse -Filter *.lean |
    Where-Object { $_.Name -notlike '*.echo.lean' } |
    Where-Object {
        (Select-String -Path $_.FullName -Pattern '^import sympy\.Basic' -Quiet) -and
        (Select-String -Path $_.FullName -Pattern '^import Lemma\.' -Quiet)
    } |
    Select-Object -ExpandProperty FullName
