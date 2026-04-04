# Same behavior as start.sh: PM2 runs server/app.mjs as process "lemma".
# Run from repo root:  .\start.ps1
#
# On Windows, PowerShell may pick npx.ps1 / npm.ps1 / pm2.ps1 (blocked by
# ExecutionPolicy). We prefer *.cmd / *.exe shims from the same install.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

Set-Location -LiteralPath $PSScriptRoot

# Optional MySQL (see server/lean/fetchLemmaMysql.mjs, server/app.mjs):
#   $env:MYSQL_HOST = '127.0.0.1'; $env:MYSQL_USER = 'user'; $env:MYSQL_PWD = 'user'; $env:MYSQL_DATABASE = 'axiom'

function Invoke-NodeCli {
    param(
        [Parameter(Mandatory)][string]$Name,
        [string[]]$Arguments = @()
    )
    $preferred = Get-Command $Name -ErrorAction SilentlyContinue -All |
        Where-Object { $_.Source -match '\.(cmd|exe)$' } |
        Select-Object -First 1
    if ($preferred) {
        & $preferred.Source @Arguments
        return
    }
    $fallback = Get-Command $Name -ErrorAction SilentlyContinue -All | Select-Object -First 1
    if ($fallback) {
        & $fallback.Source @Arguments
        return
    }
    throw "Command not found: $Name"
}

function Invoke-Pm2 {
    param(
        [Parameter(ValueFromRemainingArguments = $true)]
        [string[]]$Pm2Arguments
    )

    if (Get-Command pm2 -ErrorAction SilentlyContinue) {
        Invoke-NodeCli pm2 $Pm2Arguments
        return
    }

    $localPm2Dir = Join-Path $PSScriptRoot 'node_modules\pm2'
    if (Test-Path -LiteralPath $localPm2Dir -PathType Container) {
        Invoke-NodeCli npx (@('pm2') + $Pm2Arguments)
        return
    }

    Write-Host 'pm2 not found, installing...'
    Invoke-NodeCli npm @('install', 'pm2')
    if ($LASTEXITCODE -ne 0) {
        throw "npm install pm2 failed (exit $LASTEXITCODE)"
    }
    Invoke-NodeCli npx (@('pm2') + $Pm2Arguments)
}

Invoke-Pm2 describe lemma 2>&1 | Out-Null
if ($LASTEXITCODE -eq 0) {
    Invoke-Pm2 restart lemma
} else {
    Invoke-Pm2 start server/app.mjs --name lemma
}
if ($LASTEXITCODE -ne 0) {
    throw "pm2 start/restart failed (exit $LASTEXITCODE)"
}

Invoke-Pm2 save
if ($LASTEXITCODE -ne 0) {
    throw "pm2 save failed (exit $LASTEXITCODE)"
}

# pm2 startup only configures Linux/macOS init (systemd, launchd, …). On Windows it errors
# with "Init system not found". Use Task Scheduler / NSSM for boot, or run start.ps1 after login.
if ($env:OS -match 'Windows') {
    Write-Host 'Skipping pm2 startup on Windows (no supported init system). List already saved via pm2 save.'
} else {
    Invoke-Pm2 startup
}
