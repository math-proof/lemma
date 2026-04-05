# usage: .\ps1\push.ps1
# Retries `git push` until it succeeds (transient network / GitHub errors).
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
    $delaySec = [Math]::Min(120, 5 + ($attempt - 1) * 5)
    Write-Host "Push failed (exit code $LASTEXITCODE). Waiting ${delaySec}s before retry..."
    Start-Sleep -Seconds $delaySec
}
