param(
  [string]$Toolchain = "leanprover/lean4:v4.13.0"
)

$ErrorActionPreference = "Stop"

function Invoke-Step($Name, [scriptblock]$Body) {
  Write-Host "==> $Name"
  & $Body
  if (-not $?) { throw "Step failed: $Name" }
}

Invoke-Step "Lean toolchain" {
  elan run $Toolchain lean --version
  elan run $Toolchain lake --version
}

Invoke-Step "Lean build" {
  elan run $Toolchain lake build
}

Invoke-Step "Pinned axiom audit" {
  elan run $Toolchain lake env lean lean/PvNP/Audit.lean
}

Invoke-Step "No forbidden Lean proof escapes" {
  $paths = @((Get-ChildItem -LiteralPath "lean" -Recurse -Filter "*.lean").FullName) + @("lakefile.lean")
  $pattern = "^\s*(sorry|admit)\b|\bby\s+(sorry|admit)\b|:=\s*(sorry|admit)\b|^\s*axiom\s+[A-Za-z_]|\bby\s+native_decide\b|:=\s*native_decide\b"
  $matches = Select-String -LiteralPath $paths -Pattern $pattern
  if ($matches) {
    $matches
    throw "Forbidden Lean escape hatch found"
  }
}

Invoke-Step "Release metadata present" {
  foreach ($path in @("README.md", "INTEGRITY-CLAIMS.md", "CITATION.cff", ".zenodo.json", "lake-manifest.json", "lean-toolchain")) {
    if (-not (Test-Path -LiteralPath $path)) { throw "Missing $path" }
  }
}

Invoke-Step "Non-claims language present" {
  $matches = Select-String -LiteralPath @("README.md", "INTEGRITY-CLAIMS.md") -Pattern "does \*\*not\*\* prove|does \*\*not\*\* establish|Frege/PHP lower bound|Non-Claims"
  if (-not $matches) { throw "Required non-claims language missing" }
  $matches
}

Invoke-Step "Zenodo/CITATION v0.2.0 metadata" {
  $matches = Select-String -LiteralPath @("README.md", "CITATION.cff", ".zenodo.json") -Pattern "v0\.2\.0|10\.5281/zenodo\.20764338"
  if (-not $matches) { throw "v0.2.0 DOI/release metadata missing" }
  $matches
}

Write-Host "Release audit completed successfully."
