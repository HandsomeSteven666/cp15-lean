import CP15.CandidateAlgebra
import CP15.Caps

namespace CP15.Candidate

/-- A rational upper enclosure for the exact candidate radius. -/
theorem candidateB_lt_353_div_100 :
    CP15.candidateB < 353 / 100 := by
  have hroot : 0 < root5 := root5_pos
  have hratio : 2 / root5 < 200 / 223 := by
    apply (div_lt_iff₀ hroot).2
    have h := root5_tight_bounds.1
    nlinarith
  have hrad : 0 ≤ 1 + 2 / root5 := by positivity
  have hsqrt : Real.sqrt (1 + 2 / root5) < 69 / 50 := by
    have hs := Real.sq_sqrt hrad
    have hn := Real.sqrt_nonneg (1 + 2 / root5)
    nlinarith
  have hBsq : CP15.candidateB ^ 2 =
      6 + 2 / root5 + 4 * Real.sqrt (1 + 2 / root5) := by
    rw [← two_rho_eq_candidateB]
    exact two_rho_sq
  have hBnonneg := CP15.candidateB_pos.le
  nlinarith

/-- A slightly tighter rational enclosure, used for the ten-boundary
gap budget. -/
theorem candidateB_lt_1761_div_500 :
    CP15.candidateB < 1761 / 500 := by
  have hroot : 0 < root5 := root5_pos
  have hrootlo : (559 / 250 : ℝ) < root5 := by
    nlinarith [root5_sq]
  have hratio : 2 / root5 < 500 / 559 := by
    apply (div_lt_iff₀ hroot).2
    nlinarith
  have hrad : 0 ≤ 1 + 2 / root5 := by positivity
  have hsqrt : Real.sqrt (1 + 2 / root5) < 1377 / 1000 := by
    have hs := Real.sq_sqrt hrad
    have hn := Real.sqrt_nonneg (1 + 2 / root5)
    nlinarith
  have hBsq : CP15.candidateB ^ 2 =
      6 + 2 / root5 + 4 * Real.sqrt (1 + 2 / root5) := by
    rw [← two_rho_eq_candidateB]
    exact two_rho_sq
  have hBnonneg := CP15.candidateB_pos.le
  nlinarith

/-- A six-decimal rational enclosure of the exact candidate radius. -/
theorem candidateB_lt_352136_div_100000 :
    CP15.candidateB < 352136 / 100000 := by
  have hroot : 0 < root5 := root5_pos
  have hrootlo : (2236067 / 1000000 : ℝ) < root5 := by
    nlinarith [root5_sq]
  have hratio : 2 / root5 < 2000000 / 2236067 := by
    apply (div_lt_iff₀ hroot).2
    nlinarith
  have hrad : 0 ≤ 1 + 2 / root5 := by positivity
  have hsqrt : Real.sqrt (1 + 2 / root5) < 1376383 / 1000000 := by
    have hs := Real.sq_sqrt hrad
    have hn := Real.sqrt_nonneg (1 + 2 / root5)
    nlinarith
  have hBsq : CP15.candidateB ^ 2 =
      6 + 2 / root5 + 4 * Real.sqrt (1 + 2 / root5) := by
    rw [← two_rho_eq_candidateB]
    exact two_rho_sq
  have hBnonneg := CP15.candidateB_pos.le
  nlinarith

theorem D_candidateB_lt_12_div_5 : D CP15.candidateB < 12 / 5 := by
  have hB := CP15.candidateB_pos
  have hq : (0 : ℝ) < 353 / 100 := by norm_num
  have hrec : 4 / (353 / 100 : ℝ) < 4 / CP15.candidateB := by
    apply (div_lt_div_iff₀ hq hB).2
    nlinarith [candidateB_lt_353_div_100]
  unfold D
  have hqD : (353 / 100 : ℝ) - 4 / (353 / 100) < 12 / 5 := by norm_num
  linarith [candidateB_lt_353_div_100]

/-- The selected non-outer cap lies strictly below sqrt(2) at every
radius no larger than the exact candidate radius. -/
theorem F_lt_sqrt_two_of_le_candidateB {b : ℝ}
    (hb : 2 < b) (hbB : b ≤ CP15.candidateB) :
    F b < Real.sqrt 2 := by
  have hB := CP15.candidateB_pos
  have hrec : 4 / CP15.candidateB ≤ 4 / b := by
    apply (div_le_div_iff₀ hB (by linarith)).2
    nlinarith
  have hDb : D b < 12 / 5 := by
    have hDB := D_candidateB_lt_12_div_5
    unfold D at hDB ⊢
    linarith
  have hDbnonneg : 0 ≤ D b := (D_pos hb).le
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  by_cases hrad : 0 ≤ D b ^ 2 - 4
  · have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
      unfold F
      exact Real.sq_sqrt hrad
    have hn : 0 ≤ F b := Real.sqrt_nonneg _
    nlinarith
  · have hFzero : F b = 0 := by
      unfold F
      exact Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hrad)
    rw [hFzero]
    nlinarith

end CP15.Candidate
