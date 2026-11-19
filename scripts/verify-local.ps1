param(
  [Parameter(Mandatory=$true)][string]$LeanExe,
  [Parameter(Mandatory=$true)][string]$MathlibDirectory
)
$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path $PSScriptRoot -Parent
$buildRoot = Join-Path $repoRoot '.lake/build/lib/lean'
New-Item -ItemType Directory -Force $buildRoot | Out-Null
$resolvedLean = (Resolve-Path $LeanExe).Path
$resolvedMathlib = (Resolve-Path $MathlibDirectory).Path
$paths = @($buildRoot,"$resolvedMathlib/.lake/build/lib/lean") + @(Get-ChildItem "$resolvedMathlib/.lake/packages" -Directory | ForEach-Object { "$($_.FullName)/.lake/build/lib/lean" })
$env:LEAN_PATH = $paths -join ';'
Push-Location $repoRoot
try {
  & $resolvedLean --version
  if ($LASTEXITCODE -ne 0) { throw 'Lean version check failed' }
  foreach ($module in @('Certificate','RealBounds','CheckerCoverage','Main','Equality')) {
    Write-Output "Compiling $module from repository sources"
    & $resolvedLean -o "$buildRoot/$module.olean" "$module.lean"
    if ($LASTEXITCODE -ne 0) { throw "Compilation failed: $module" }
  }
  Write-Output 'All five proof modules compiled successfully.'
} finally { Pop-Location }
