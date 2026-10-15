param([switch]$Clean)
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if ($Clean) {
        & lake clean
        if ($LASTEXITCODE -ne 0) { throw 'Lake clean failed.' }
    }
    & lake exe cache get
    if ($LASTEXITCODE -ne 0) { throw 'Mathlib cache retrieval failed.' }
    & lake build CP15
    if ($LASTEXITCODE -ne 0) { throw 'Root library build failed.' }
    $auditOutput = & lake env lean tools/SubmissionAudit.lean 2>&1
    if ($LASTEXITCODE -ne 0) { throw ($auditOutput -join "`n") }
    $auditOutput | Write-Output
    $report = $auditOutput -join "`n"
    foreach ($theoremName in @('centerOptimal_candidate', 'originalValue_eq_candidate', 'global_unique_optimal_packing15')) {
        $pattern = "'CP15\." + [regex]::Escape($theoremName) + "' depends on axioms:\s*\[([^\]]*)\]"
        $matchResult = [regex]::Match($report, $pattern)
        if (-not $matchResult.Success) { throw "No axiom audit found for $theoremName." }
        foreach ($axiomName in ($matchResult.Groups[1].Value -split ',')) {
            if ($axiomName.Trim() -notin @('propext','Classical.choice','Quot.sound')) {
                throw "Unexpected axiom in $theoremName : $axiomName"
            }
        }
    }
    Write-Output 'All three endpoints passed the standard-axiom audit.'
} finally {
    Pop-Location
}
