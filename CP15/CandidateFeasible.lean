import CP15.CandidatePairs
import CP15.CandidateRadius

namespace CP15.Candidate

/-- The exact proposed configuration, scaled to separation two, fits in the
enclosing disk of radius `candidateB`. This is a lower-bound construction,
not a global-optimality statement. -/
theorem center_feasible : CenterFeasible 15 CP15.candidateB := by
  refine ⟨pointAtSeparationTwo, ?_, ?_⟩
  · intro i
    change ‖scale 2 point i‖ ≤ CP15.candidateB
    rw [norm_scale 2 (by norm_num)]
    have h := all_radius_le i
    rw [← two_rho_eq_candidateB]
    nlinarith
  · intro i j hij
    change 2 ≤ dist (scale 2 point i) (scale 2 point j)
    rw [dist_scale 2 (by norm_num)]
    have h := separated_point i j hij
    nlinarith

end CP15.Candidate
