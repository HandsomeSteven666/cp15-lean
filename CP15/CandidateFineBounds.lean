import CP15.CandidateBounds

namespace CP15.Candidate

/-- The fine alternating cover uses this rational upper enclosure. Its
strict relation to the exact candidate is proved, not supplied by a file. -/
theorem candidateB_lt_3521357_div_1000000 :
    CP15.candidateB < 3521357 / 1000000 := by
  have hroot : 0 < root5 := root5_pos
  have hrootlo : (223606797 / 100000000 : ℝ) < root5 := by
    nlinarith [root5_sq]
  have hratio : 2 / root5 < 200000000 / 223606797 := by
    apply (div_lt_iff₀ hroot).2
    nlinarith
  have hrad : 0 ≤ 1 + 2 / root5 := by positivity
  have hsqrt : Real.sqrt (1 + 2 / root5) < 137638193 / 100000000 := by
    have hs := Real.sq_sqrt hrad
    have hn := Real.sqrt_nonneg (1 + 2 / root5)
    nlinarith
  have hBsq : CP15.candidateB ^ 2 =
      6 + 2 / root5 + 4 * Real.sqrt (1 + 2 / root5) := by
    rw [← two_rho_eq_candidateB]
    exact two_rho_sq
  have hBnonneg := CP15.candidateB_pos.le
  nlinarith

end CP15.Candidate
