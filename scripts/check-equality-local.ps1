param(
  [Parameter(Mandatory=$true)][string]$LeanExe,
  [Parameter(Mandatory=$true)][string]$MathlibDirectory
)
$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path $PSScriptRoot -Parent
$buildRoot = Join-Path $repoRoot '.lake/build/lib/lean'
$paths = @($buildRoot,"$MathlibDirectory/.lake/build/lib/lean") + @(Get-ChildItem "$MathlibDirectory/.lake/packages" -Directory | ForEach-Object { "$($_.FullName)/.lake/build/lib/lean" })
$env:LEAN_PATH = $paths -join ';'
Push-Location $repoRoot
try {
  if ((Get-Item RealBounds.lean).LastWriteTime -gt (Get-Item "$buildRoot/RealBounds.olean").LastWriteTime) {
    & $LeanExe -o "$buildRoot/RealBounds.olean" RealBounds.lean
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  }
  if ((Get-Item "$buildRoot/RealBounds.olean").LastWriteTime -gt (Get-Item "$buildRoot/Main.olean").LastWriteTime) {
    & $LeanExe -o "$buildRoot/Main.olean" Main.lean
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  }
  & $LeanExe Equality.lean
  exit $LASTEXITCODE
} finally { Pop-Location }
