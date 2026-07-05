param(
    [Parameter(Position = 0)]
    [ValidateNotNullOrEmpty()]
    [ValidatePattern('^[a-zA-Z0-9_]+$')]
    [string] $Table = 'lemma',

    [Parameter()]
    [ValidatePattern('^[a-zA-Z0-9_-]+$')]
    [string] $Project
)
# usage, sync default table: lemma
# .\ps1\synchronize.ps1
# any InnoDB table in schema axiom (identifier-safe name)
# .\ps1\synchronize.ps1 -Table other_table
# git pull on remote before sync (repo path: ~/github/<Project>)
# .\ps1\synchronize.ps1 -Project lean
# .\ps1\synchronize.ps1 -Project lean -Table lemma
if ($Project) {
    Write-Host "git pull github/$Project on ${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}..."
    ssh "${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}" "git -C github/$Project pull"
    if ($LASTEXITCODE -ne 0) {
        throw "git pull github/$Project failed with exit code $LASTEXITCODE"
    }
}

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
Write-Host "Discard Tablespace Output: $sshOutput"
# send the files from the table axiom.$Table in the data directory: $local_datadir\axiom\$Table#P#p*.ibd to the remote server
scp "$local_datadir\axiom\$Table*.ibd" ${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}:${remote_datadir}axiom
# Linux is case-sensitive; WAMP may use lemma#P#pN.ibd while Linux MySQL uses lemma#p#pN.ibd
ssh "${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}" "cd ${remote_datadir}axiom && for f in ${Table}#P#p*.ibd; do [ -e `"`$f`" ] || continue; mv `"`$f`" `"`$(echo `"`$f`" | sed 's/#P#p/#p#p/')`"; done && chown mysql:mysql ${Table}*.ibd"
if ($LASTEXITCODE -ne 0) {
    throw "normalize partition .ibd names / chown failed with exit code $LASTEXITCODE"
}
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PWD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'ALTER TABLE $Table IMPORT TABLESPACE'"
$sshOutput = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Host "Import Tablespace Output: $sshOutput"

# test : check the number of rows in the local and remote table
$mysqlCommand = "$mysql -u $env:REMOTE_MYSQL_USER -p$env:REMOTE_MYSQL_PWD -P $env:REMOTE_MYSQL_PORT -D axiom -e 'select count(*) from $Table'"
$remoteCount = ssh $env:REMOTE_MYSQL_USER@$env:REMOTE_MYSQL_HOST $mysqlCommand
Write-Host "Remote $Table count: $remoteCount"

