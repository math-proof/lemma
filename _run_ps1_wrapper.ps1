Set-Location E:\github\py
$env:PYTHONIOENCODING = "utf-8"
$env:PYTHONUTF8 = "1"
$env:MYSQL_PWD = "prod"
$env:MYSQL_HOST = "localhost"
$outLog = "E:\github\py\run_ps1_out.txt"
$errLog = "E:\github\py\run_ps1_err.txt"
$exitLog = "E:\github\py\run_ps1_exit.txt"
$stdinFile = "E:\github\py\_run_ps1_stdin.txt"
Remove-Item $outLog, $errLog, $exitLog -ErrorAction SilentlyContinue
Set-Content -Path $stdinFile -Value "`n" -NoNewline -Encoding ascii
$p = Start-Process -FilePath "pwsh" `
  -ArgumentList @("-NoProfile","-ExecutionPolicy","Bypass","-File","E:\github\py\ps1\run.ps1") `
  -WorkingDirectory "E:\github\py" `
  -RedirectStandardInput $stdinFile `
  -RedirectStandardOutput $outLog `
  -RedirectStandardError $errLog `
  -PassThru -NoNewWindow
$p.Id | Set-Content "E:\github\py\_run_ps1_wrapper.pid" -Encoding ascii
Write-Host "STARTED pid=$($p.Id)"
$p.WaitForExit()
$code = $p.ExitCode
$code | Set-Content $exitLog -Encoding ascii
Write-Host "FINISHED exit=$code"
