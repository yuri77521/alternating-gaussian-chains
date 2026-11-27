# Local development helper. Pass direct Lean flags or use -Lake for a Lake command.
param([switch]$Lake, [Parameter(ValueFromRemainingArguments=$true)][string[]]$Arguments)
$ErrorActionPreference = 'Stop'
$env:LEAN_NUM_THREADS = '1'
$slot = [Threading.Semaphore]::new(4, 4, 'Local\GaussianStudyKernel4')
$null = $slot.WaitOne()
try {
    Push-Location $PSScriptRoot
    if ($Lake) {
        & lake @Arguments
    } else {
        & lake env lean @Arguments
    }
    $result = $LASTEXITCODE
} finally {
    Pop-Location
    $null = $slot.Release()
    $slot.Dispose()
}
exit $result
