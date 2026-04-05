# Stop the PM2 app named `lemma` (opposite of start.ps1). Run from repo root: .\stop.ps1
# Use `pm2 delete lemma` instead if you want it removed from PM2’s list entirely.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

Set-Location -LiteralPath $PSScriptRoot

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

    throw 'pm2 not found. Run from repo after npm install, or install pm2 globally.'
}

Invoke-Pm2 describe lemma 2>&1 | Out-Null
if ($LASTEXITCODE -ne 0) {
    Write-Host 'No PM2 process named lemma.'
    exit 0
}

Invoke-Pm2 stop lemma
if ($LASTEXITCODE -ne 0) {
    throw "pm2 stop lemma failed (exit $LASTEXITCODE)"
}

Invoke-Pm2 save
if ($LASTEXITCODE -ne 0) {
    throw "pm2 save failed (exit $LASTEXITCODE)"
}

Write-Host 'lemma stopped. Start again with .\start.ps1'
