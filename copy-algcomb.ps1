# copy-algcomb.ps1
# Mirrors E:\github\algebraic-combinatorics\AlgebraicCombinatorics\ into
# E:\github\lean\AlgebraicCombinatorics\ using robocopy (only *.lean files).
#
# Run from PowerShell 7 (pwsh) or Windows PowerShell:
#   pwsh -File E:\github\lean\copy-algcomb.ps1
#
# It is safe to re-run: robocopy with /E does not delete files in the
# destination, so any *.lean you already have (from a partial vendor) is
# preserved or overwritten with the canonical source. Bytes should be
# identical either way.
#
# Exit codes (this script):
#   0  = success (one or more files copied, or dest already up to date)
#   2  = source path not found
#   3  = robocopy reported a real error (exit code >= 8)

$ErrorActionPreference = 'Stop'

$src = 'E:\github\algebraic-combinatorics\AlgebraicCombinatorics'
$dst = 'E:\github\lean\AlgebraicCombinatorics'

if (-not (Test-Path -LiteralPath $src)) {
    Write-Error "Source not found: $src"
    exit 2
}

# Make sure the destination root exists; robocopy will create subdirs.
New-Item -ItemType Directory -Force -Path $dst | Out-Null

$before = (Get-ChildItem -Recurse -File -Path $dst -Filter '*.lean' -ErrorAction SilentlyContinue |
           Measure-Object).Count
$beforeBytes = (Get-ChildItem -Recurse -File -Path $dst -Filter '*.lean' -ErrorAction SilentlyContinue |
                Measure-Object -Property Length -Sum).Sum

# robocopy flags:
#   /E       recurse, including empty dirs
#   *.lean   only copy .lean files
#   /NFL /NDL /NJH /NJS /NP   quiet output (no per-file / per-dir listings)
#   /R:0 /W:0   no retries, no wait
#   /BYTES    print sizes as raw bytes
$robocopyArgs = @(
    $src
    $dst
    '*.lean'
    '/E'
    '/NFL','/NDL','/NJH','/NJS','/NP'
    '/R:0','/W:0'
    '/BYTES'
)

# Use the older STA call path that returns exit code synchronously.
$rc = & robocopy.exe @robocopyArgs

# robocopy exit codes 0..7 are success; >=8 are errors.
if ($rc -ge 8) {
    Write-Error "robocopy failed with exit code $rc"
    exit 3
}

$after = (Get-ChildItem -Recurse -File -Path $dst -Filter '*.lean' -ErrorAction SilentlyContinue |
          Measure-Object).Count
$afterBytes = (Get-ChildItem -Recurse -File -Path $dst -Filter '*.lean' -ErrorAction SilentlyContinue |
               Measure-Object -Property Length -Sum).Sum

$copied = $after - $before
$bytesAdded = $afterBytes - $beforeBytes

Write-Host ''
Write-Host '== copy-algcomb summary =='
Write-Host ("  source       : {0}" -f $src)
Write-Host ("  destination  : {0}" -f $dst)
Write-Host ("  .lean files  : {0} -> {1}  (delta {2:+#;-#;0})" -f $before, $after, $copied)
Write-Host ("  total bytes  : {0:N0} -> {1:N0}  (delta {2:+#,#;-#,#;0})" -f $beforeBytes, $afterBytes, $bytesAdded)
Write-Host ("  robocopy rc  : {0}  (0=no change, 1=copied, 2=extras in dst, 3=both)" -f $rc)
Write-Host ''
Write-Host 'Next steps:'
Write-Host '  1. Confirm E:\github\lean\lakefile.toml has the AlgebraicCombinatorics lean_lib block'
Write-Host '     (already appended by the assistant; if missing, add:'
Write-Host '         [[lean_lib]]'
Write-Host '         name = "AlgebraicCombinatorics"'
Write-Host '         leanOptions = { autoImplicit = false }'
Write-Host '     )'
Write-Host '  2. From a shell in E:\github\lean:'
Write-Host '         lake update'
Write-Host '         lake build AlgebraicCombinatorics 2>&1 | tee build.log'
Write-Host '  3. If the build fails, paste the first ~50 lines of build.log back.'
