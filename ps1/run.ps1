
while ($true) {
    # Set up process start info
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = "python"
    $psi.Arguments = "run.py"
    # Run in the same window
    $psi.UseShellExecute = $false
    # Direct output to console
    $psi.RedirectStandardOutput = $false
    # Direct errors to console
    $psi.RedirectStandardError = $false

    # Start the process
    $process = [System.Diagnostics.Process]::Start($psi)

    # Wait for 2 minutes (120,000 milliseconds)
    $exited = $process.WaitForExit(120000)

    if (-not $exited) {
        # Kill the process and all its child processes forcefully
        Start-Process -FilePath "taskkill" -ArgumentList "/PID", $process.Id, "/T", "/F" -Wait -NoNewWindow
        $exit_status = 124
    } else {
        $exit_status = $process.ExitCode
    }

    # Handle exit status
    switch ($exit_status) {
        124 {
            Write-Host "Python program was halted because it took more than 2 minutes."
            break
        }
        0 {
            Write-Host "Python program completed within the time limit."
            break
        }
        default {
            Write-Host "An error occurred. Exit status: $_"
            continue
        }
    }

    # Break out of loop if successful
    if ($exit_status -eq 0) {
        break
    }
}

# Wait for user input
Read-Host "Please enter any key to continue"

# Run subsequent Python scripts
python -c "exec(open('./util/hierarchy.py').read())"
python -c "exec(open('./util/function.py').read())"