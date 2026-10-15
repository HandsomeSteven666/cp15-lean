import CP15.Original
import CP15.Scaling

namespace CP15

/-- Radius of the proposed fifteen-center configuration at separation two. -/
noncomputable def candidateB : ℝ :=
  Real.sqrt (6 + 2 / Real.sqrt 5 + 4 * Real.sqrt (1 + 2 / Real.sqrt 5))

theorem candidateB_pos : 0 < candidateB := by
  unfold candidateB
  positivity

/-- Final scaling bridge. The premise is precisely the unproved global
center-radius assertion; this theorem does not discharge that premise. -/
theorem originalValue_eq_candidate_of_centerOptimal
    (h : CenterOptimal 15 candidateB) :
    originalValue = 2 / candidateB := by
  rw [originalValue_eq_d15]
  exact d15_eq_of_pointOptimal
    (center_optimal_to_point_optimal candidateB_pos h)

end CP15
