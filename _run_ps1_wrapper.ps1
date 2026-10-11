Set-Location E:\github\py
$outLog = 'E:\github\py\run_ps1_out.txt'
$errLog = 'E:\github\py\run_ps1_err.txt'
$exitLog = 'E:\github\py\run_ps1_exit.txt'
$stdinFile = 'E:\github\py\_run_ps1_stdin.txt'
Remove-Item $outLog, $errLog, $exitLog -ErrorAction SilentlyContinue
# One newline ready for Read-Host after successful run.py
Set-Content -Path $stdinFile -Value "`n" -NoNewline -Encoding ascii

$p = Start-Process -FilePath 'pwsh' `
  -ArgumentList @('-NoProfile','-ExecutionPolicy','Bypass','-File','E:\github\py\ps1\run.ps1') `
  -WorkingDirectory 'E:\github\py' `
  -RedirectStandardInput $stdinFile `
  -RedirectStandardOutput $outLog `
  -RedirectStandardError $errLog `
  -PassThru -NoNewWindow

$p.Id | Set-Content 'E:\github\py\_run_ps1_wrapper.pid' -Encoding ascii
Write-Host "STARTED pid=$($p.Id)"
$p.WaitForExit()
$code = $p.ExitCode
$code | Set-Content $exitLog -Encoding ascii
Write-Host "FINISHED exit=$code"
