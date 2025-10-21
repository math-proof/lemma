# usage: 
# . ps1/mathlib.ps1
param(
    [bool]$refresh = $false
)

# Check if MYSQL_USER is set
if (-not $env:MYSQL_USER) {
    Write-Host "MYSQL_USER is not set. Please ensure it is set in your environment."
    exit 1
}
[Console]::OutputEncoding = [Text.Encoding]::UTF8
$OutputEncoding = [Text.Encoding]::UTF8

# Generate json/mathlib.jsonl if missing
if ($refresh || -not (Test-Path "json/mathlib.jsonl")) {
    Write-Host "Building Mathlib..."
    lake build Mathlib
    Write-Host "Generating mathlib.jsonl..."
    New-Item -Path "json/mathlib.jsonl" -ItemType File -Force
    # lake env lean sympy/printing/mathlib.lean | Out-File "json/mathlib.jsonl" -Encoding utf8
    cmd /c "lake env lean sympy/printing/mathlib.lean" | Tee-Object -FilePath "json/mathlib.jsonl" -Append
    # cmd /c "lake setup-file sympy/printing/mathlib.lean" | Tee-Object -FilePath "json/mathlib.jsonl" -Append
}

# Generate json/mathlib.tsv if missing
if ($refresh || -not (Test-Path "json/mathlib.tsv")) {
    # Read all lines, parse JSON, produce TSV, write as UTF8
    $tsv = Get-Content -Path "json/mathlib.jsonl" | ForEach-Object {
        try {
            $obj = $_ | ConvertFrom-Json -ErrorAction Stop
            # handle missing/empty properties gracefully
            $name = ConvertTo-Json $obj.name -Compress
            $name = $name.Trim('"')
            $type = ConvertTo-Json $obj.type -Compress
            $type = $type.Trim('"')
            # produce a tab-separated string
            "$name`t$type"
        } catch {
            # if line isn't valid JSON, skip or log; here we output an empty pair
            Write-Warning "Skipping invalid JSON line: $_"
            "`t"
        }
    }
    $tsv | Out-File -FilePath "json/mathlib.tsv" -Encoding utf8
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

# Run MySQL import and log output
Get-Content "sql/insert/mathlib.sql" | mysql --defaults-extra-file="$tempConfigPath" -D axiom *>&1 | Tee-Object -FilePath "test.log"

# Check if the error indicates missing table
$pattern = "ERROR \d+ \(\w+\) at line \d+: Table 'axiom\.mathlib' doesn't exist"
if (Select-String -Path "test.log" -Pattern $pattern -Quiet) {
    Write-Host "Table 'mathlib' does not exist. Creating it..."
    
    # Execute create SQL script
    Get-Content "sql/create/mathlib.sql" | mysql --defaults-extra-file="$tempConfigPath" -D axiom
    
    if ($?) {
        Write-Host "Table 'mathlib' created successfully. Re-running script..."
        & $MyInvocation.MyCommand.Path @args
    } else {
        Write-Host "Failed to create table 'mathlib'."
        exit 1
    }
}

Remove-Item $tempConfigPath -Force
