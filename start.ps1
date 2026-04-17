# PM2 runs server/app.mjs as process "lemma".
# Run from repo root:  .\start.ps1
#
# Multi-processing: Node is one thread per process; one stuck request can block that process.
# PM2 cluster mode runs several Node workers; other workers still accept new connections.
#   Default: 8 Node workers (PM2 -i 8). Override:
#   $env:LEAN_WORKERS = 'max'   # one worker per logical CPU (PM2 -i max)
#   $env:LEAN_WORKERS = '4'     # exactly four workers
#   $env:LEAN_WORKERS = '1'     # single process
# After changing LEAN_WORKERS, run:  pm2 delete lemma  then  .\start.ps1
# (pm2 restart lemma keeps the previous instance count.)
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

$pm2Instances = '8'
$lw = $env:LEAN_WORKERS
if ($null -ne $lw -and $lw.Trim() -ne '') {
    $t = $lw.Trim()
    if ($t -eq 'max') {
        $pm2Instances = 'max'
    }
    elseif ($t -eq '1') {
        $pm2Instances = '1'
    }
    elseif ($t -match '^[1-9]\d*$') {
        $pm2Instances = $t
    }
    else {
        Write-Warning "LEAN_WORKERS='$t' not recognized; using 8. Use 1, a positive integer, or max."
    }
}

Invoke-Pm2 describe lemma 2>&1 | Out-Null
if ($LASTEXITCODE -eq 0) {
    Invoke-Pm2 restart lemma
} else {
    Invoke-Pm2 @('start', 'server/app.mjs', '--name', 'lemma', '-i', $pm2Instances)
}
if ($LASTEXITCODE -ne 0) {
    throw "pm2 start/restart failed (exit $LASTEXITCODE)"
}

Write-Host "PM2 lemma: pm2 list. New installs use -i $pm2Instances (set LEAN_WORKERS); pm2 restart keeps existing instance count."

Invoke-Pm2 save
if ($LASTEXITCODE -ne 0) {
    throw "pm2 save failed (exit $LASTEXITCODE)"
}

# Same idea as ../label/start.ps1: print the exact prefix to stream logs (PM2 app name is `lemma`).
$pm2CmdParts = @()
if (Get-Command pm2 -ErrorAction SilentlyContinue) {
    $preferred = Get-Command pm2 -ErrorAction SilentlyContinue -All |
        Where-Object { $_.Source -match '\.(cmd|exe)$' } |
        Select-Object -First 1
    if ($preferred) {
        $pm2CmdParts = @($preferred.Source)
    }
    else {
        $fb = Get-Command pm2 -ErrorAction SilentlyContinue -All | Select-Object -First 1
        if ($fb) {
            $pm2CmdParts = @($fb.Source)
        }
        else {
            $pm2CmdParts = @('pm2')
        }
    }
}
elseif (Test-Path -LiteralPath (Join-Path $PSScriptRoot 'node_modules\pm2') -PathType Container) {
    $npxCmd = Get-Command npx.cmd -ErrorAction SilentlyContinue
    if ($npxCmd) {
        $pm2CmdParts = @($npxCmd.Source, 'pm2')
    }
    else {
        $pm2CmdParts = @('npx', 'pm2')
    }
}
else {
    $pm2CmdParts = @('pm2')
}

function Quote-IfNeeded([string]$Text) {
    if ($null -eq $Text -or $Text -eq '') {
        return $Text
    }
    if ($Text -match '\s') {
        return '"' + $Text.Replace('"', '""') + '"'
    }
    return $Text
}

# Paths like D:\Program Files\... must be quoted; in PowerShell the call operator & is required.
$quotedJoin = ($pm2CmdParts | ForEach-Object { Quote-IfNeeded $_ }) -join ' '
$withLogs = ($quotedJoin + ' logs lemma').Trim()
$viewerLine = if ($pm2CmdParts[0] -match '\s') {
    '& ' + $withLogs
}
else {
    $withLogs
}
Write-Host "Use the following command to view logs:`n$viewerLine"

# pm2 startup only configures Linux/macOS init (systemd, launchd, …). On Windows it errors
# with "Init system not found". Use Task Scheduler / NSSM for boot, or run start.ps1 after login.
if ($env:OS -notmatch 'Windows') {
    Invoke-Pm2 startup
}
