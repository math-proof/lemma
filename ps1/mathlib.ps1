# usage: powershell sh/mathlib.ps1

# Check if MYSQL_USER is set
if (-not $env:MYSQL_USER) {
    Write-Host "MYSQL_USER is not set. Please ensure it is set in your environment."
    exit 1
}

# Generate json/mathlib.jsonl if missing
if (-not (Test-Path "json/mathlib.jsonl")) {
    Write-Host "Building Mathlib..."
    Measure-Command { & lake build Mathlib 2>&1 } | Out-Host
    Write-Host "Generating mathlib.jsonl..."
    Measure-Command { lake env lean sympy/printing/mathlib.lean | Out-File "json/mathlib.jsonl" -Encoding utf8 } | Out-Host
}

# Generate json/mathlib.tsv if missing
if (-not (Test-Path "json/mathlib.tsv")) {
    # Read all lines, parse JSON, produce TSV, write as UTF8
    $tsv = Get-Content -Path "json/mathlib.jsonl" | ForEach-Object {
        try {
            $obj = $_ | ConvertFrom-Json -ErrorAction Stop
            # handle missing/empty properties gracefully
            $name = if ($obj.name) { $obj.name } else { "" }
            $type = if ($obj.type) { $obj.type } else { "" }
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

# Run MySQL import and log output
Get-Content "sql/insert/mathlib.sql" | mysql --local-infile=1 -u$env:MYSQL_USER -p$env:MYSQL_PASSWORD -P$env:MYSQL_PORT -D axiom *>&1 | Tee-Object -FilePath "test.log"

# Check if the error indicates missing table
$pattern = "ERROR \d+ \(\w+\) at line \d+: Table 'axiom\.mathlib' doesn't exist"
if (Select-String -Path "test.log" -Pattern $pattern -Quiet) {
    Write-Host "Table 'mathlib' does not exist. Creating it..."
    
    # Execute create SQL script
    Get-Content "sql/create/mathlib.sql" | mysql -u$env:MYSQL_USER -p$env:MYSQL_PASSWORD -P$env:MYSQL_PORT -D axiom
    
    if ($?) {
        Write-Host "Table 'mathlib' created successfully. Re-running script..."
        & $MyInvocation.MyCommand.Path @args
    } else {
        Write-Host "Failed to create table 'mathlib'."
        exit 1
    }
}