# usage: .\ps1\push.ps1
# Endless retries: `while ($true)` until `git push` exits 0 (only then `exit 0`).
# Backoff grows without a cap: 5s, 10s, 15s, …
[Console]::OutputEncoding = [Text.Encoding]::UTF8
$OutputEncoding = [Text.Encoding]::UTF8

$__file__ = $MyInvocation.MyCommand.Path | Resolve-Path
$root = Split-Path -Path (Split-Path -Path $__file__ -Parent) -Parent
Set-Location -LiteralPath $root

$attempt = 0
while ($true) {
    $attempt++
    Write-Host "git push (attempt $attempt)..."
    git push
    if ($LASTEXITCODE -eq 0) {
        Write-Host "Push succeeded."
        exit 0
    }
    $delaySec = 5 + ($attempt - 1) * 5
    Write-Host "Push failed (exit code $LASTEXITCODE). Waiting ${delaySec}s before retry..."
    Start-Sleep -Seconds $delaySec
}
