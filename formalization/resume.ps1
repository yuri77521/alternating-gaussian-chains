# Run in the existing checkout after a restart or an interrupted verification.
[CmdletBinding()]
param([int]$BatchSize = 2, [string]$UpstreamGit)
$ErrorActionPreference = 'Stop'
$python = (Get-Command python -CommandType Application -ErrorAction Stop | Select-Object -First 1).Source
$env:LEAN_NUM_THREADS = '1'
$env:PYTHONUTF8 = '1'
$argsForBuild = @('-B', (Join-Path $PSScriptRoot 'rebuild.py'), '--resume', '--batch-size', "$BatchSize")
if ($UpstreamGit) {
    $argsForBuild += @('--upstream-git', (Resolve-Path -LiteralPath $UpstreamGit).Path)
}
if (Test-Path (Join-Path $PSScriptRoot '.lake/packages/mathlib/.git')) {
    $argsForBuild += '--installed-dependencies'
}
& $python @argsForBuild
exit $LASTEXITCODE
