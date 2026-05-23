param(
    [Parameter(Position = 0)]
    [ValidateNotNullOrEmpty()]
    [ValidatePattern('^[a-zA-Z0-9_]+$')]
    [string] $Table = 'lemma'
)
# usage:
#   . .\ps1\synchronize.ps1                    # default table: lemma
#   . .\ps1\synchronize.ps1 -Table other_table # any InnoDB table in schema axiom (identifier-safe name)
# Run the MySQL command, use -N to skip headers and -B for batch output.
$local_datadir = mysql -u"$env:USERNAME" --default-character-set=utf8mb4 -N -B -D axiom -e "SHOW VARIABLES WHERE Variable_name = 'datadir'" |
    ForEach-Object { $_.Split("`t")[1] }
Write-Host "Data Directory is: $local_datadir"


# We construct the command string to run on the Linux side.
$mysql = "/usr/local/mysql/bin/mysql"
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PWD -P $env:REMOTE_MYSQL_PORT -s -N -e 'SHOW VARIABLES WHERE Variable_name = `"datadir`"'"
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
if ($sshOutput) {
    # Split by whitespace and take the last element (the path)
    $remote_datadir = $sshOutput -split '\s+' | Select-Object -Last 1
    Write-Host "Remote DataDir is: $remote_datadir"
}

$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PWD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'ALTER TABLE $Table DISCARD TABLESPACE'"
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Debug "Discard Tablespace Output: $sshOutput"
# send the files from the table axiom.$Table in the data directory: $local_datadir\axiom\$Table#P#p*.ibd to the remote server
scp "$local_datadir\axiom\$Table*.ibd" ${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}:${remote_datadir}axiom
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PWD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'ALTER TABLE $Table IMPORT TABLESPACE'"
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Debug "Import Tablespace Output: $sshOutput"

# test : check the number of rows in the local and remote table
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PWD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'select count(*) from $Table'"
$remoteCount = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Debug "Remote $Table count: $remoteCount"

# until git pull; do sleep 1; done
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST "git pull"
