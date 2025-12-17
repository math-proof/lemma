# usage:
# . .\ps1\synchronize.ps1
# Create a temporary config file with .ini extension
$tempConfigPath = [IO.Path]::ChangeExtension((New-TemporaryFile).FullName, '.ini')
@"
[client]
user = $env:MYSQL_USER
password = $env:MYSQL_PASSWORD
port = $env:MYSQL_PORT
default-character-set=utf8mb4
"@ | Set-Content $tempConfigPath

# Run the MySQL command, use -N to skip headers and -B for batch output.
# Select-Object -Last 1 grabs the value from the second column.
$local_datadir = mysql --defaults-extra-file="$tempConfigPath" -N -B -D axiom -e "SHOW VARIABLES WHERE Variable_name = 'datadir'" | 
    ForEach-Object { $_.Split("`t")[1] }
Remove-Item $tempConfigPath -Force -ErrorAction SilentlyContinue
Write-Host "Data Directory is: $local_datadir"


# We construct the command string to run on the Linux side.
$mysql = "/usr/local/mysql/bin/mysql"
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PASSWORD -P $env:REMOTE_MYSQL_PORT -s -N -e 'SHOW VARIABLES WHERE Variable_name = `"datadir`"'"
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
if ($sshOutput) {
    # Split by whitespace and take the last element (the path)
    $remote_datadir = $sshOutput -split '\s+' | Select-Object -Last 1
    Write-Host "Remote DataDir is: $remote_datadir"
}

$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PASSWORD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'ALTER TABLE lemma DISCARD TABLESPACE'"
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Debug "Discard Tablespace Output: $sshOutput"
# send the files from the table axiom.lemma in the data directory: $local_datadir\axiom\lemma#P#p*.ibd to the remote server
scp "$local_datadir\axiom\lemma*.ibd" ${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}:${remote_datadir}axiom
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PASSWORD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'ALTER TABLE lemma IMPORT TABLESPACE'"
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Debug "Import Tablespace Output: $sshOutput"

# test : check the number of rows in the local and remote lemma table
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PASSWORD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'select count(*) from lemma'"
$remoteCount = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Debug "Remote lemma count: $remoteCount"

# until git pull; do sleep 1; done
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST "git pull"
