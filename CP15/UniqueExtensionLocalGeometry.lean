import CP15.CandidateAlgebra

namespace CP15.Candidate

/-- The slope in the seed coordinates is strictly between one and `sqrt 3`.
The second inequality is the strict numerical margin used by the local
boundary completion argument. -/
theorem ratio_local_bounds :
    1 < c / s ∧ (c / s) ^ 2 < 3 := by
  constructor
  · have hs := s_pos
    have hsimple := simple_bounds
    have hsc : s < c := by
      rcases hsimple with ⟨_, hsupper, hclower, _, _, _, _, _⟩
      linarith
    exact (lt_div_iff₀ hs).2 (by simpa using hsc)
  · rw [c_div_s_sq]
    have hrootpos := root5_pos
    have hratio : 2 / root5 < 1 := by
      apply (div_lt_iff₀ hrootpos).2
      have hroot := root5_bounds.1
      linarith
    linarith

end CP15.Candidate

namespace CP15

/-- A locally feasible point near the seed boundary point `(1,a+2)` must
coincide with it. The two contact constraints come from `(1,a)` and
`(-1,a+2)`, while the last inequality is the enclosing disk constraint.
All calculations are over exact real inequalities. -/
theorem seed_boundary_point_unique_within_radius_two
    (a dx dy : ℝ)
    (ha : 1 < a)
    (ha2 : a ^ 2 < 3)
    (hnear : dx ^ 2 + dy ^ 2 ≤ 4)
    (hinner : dx ^ 2 + (dy + 2) ^ 2 ≥ 4)
    (houter : (dx + 2) ^ 2 + dy ^ 2 ≥ 4)
    (hdisk : dx ^ 2 + dy ^ 2 + 2 * dx + 2 * (a + 2) * dy ≤ 0) :
    dx = 0 ∧ dy = 0 := by
  let S : ℝ := dx ^ 2 + dy ^ 2
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hSle4 : S ≤ 4 := by
    simpa [S] using hnear
  have hdylo : -S / 4 ≤ dy := by
    dsimp [S] at *
    nlinarith [sq_nonneg dy]
  have hdxlo : -S / 4 ≤ dx := by
    dsimp [S] at *
    nlinarith [sq_nonneg dx]
  have hdyhi : 4 * (a + 2) * dy ≤ -S := by
    dsimp [S] at *
    nlinarith
  have hApos : 0 < a + 2 := by linarith
  have hdy_nonpos : dy ≤ 0 := by
    nlinarith
  have hdxhi : 4 * dx ≤ a * S := by
    have hmul : -(a + 2) * S / 2 ≤ 2 * (a + 2) * dy := by
      have hprod := mul_nonneg (by linarith : 0 ≤ a + 2)
        (by linarith : 0 ≤ dy + S / 4)
      nlinarith
    dsimp [S] at *
    nlinarith
  have hdxlo' : -(a * S) / 4 ≤ dx := by
    have hprod := mul_nonneg (by linarith : 0 ≤ a - 1) hSnonneg
    nlinarith
  have hdxup' : dx ≤ (a * S) / 4 := by
    nlinarith [hdxhi]
  have hdxsq : dx ^ 2 ≤ (a * S / 4) ^ 2 := by
    have hprod := mul_nonneg
      (by linarith : 0 ≤ a * S / 4 - dx)
      (by linarith : 0 ≤ a * S / 4 + dx)
    nlinarith
  have hdysq : dy ^ 2 ≤ (S / 4) ^ 2 := by
    have hdyupper : dy ≤ S / 4 := by linarith [hdy_nonpos, hSnonneg]
    have hprod := mul_nonneg
      (by linarith : 0 ≤ S / 4 - dy)
      (by linarith : 0 ≤ S / 4 + dy)
    nlinarith
  have hquad : S ≤ (a ^ 2 + 1) * S ^ 2 / 16 := by
    dsimp [S] at *
    nlinarith [hdxsq, hdysq]
  have hfactorprod : (a ^ 2 + 1) * S < 16 := by
    have hcoef : 0 < a ^ 2 + 1 := by positivity
    calc
      (a ^ 2 + 1) * S ≤ (a ^ 2 + 1) * 4 :=
        mul_le_mul_of_nonneg_left hSle4 hcoef.le
      _ < 4 * 4 := by nlinarith
      _ = 16 := by norm_num
  by_cases hSpos : 0 < S
  · have hsmall : (a ^ 2 + 1) * S ^ 2 / 16 < S := by
      have hfactor : 0 < 1 - (a ^ 2 + 1) * S / 16 := by
        nlinarith
      have hprod := mul_pos hSpos hfactor
      nlinarith
    linarith
  · have hSz : S = 0 := le_antisymm (le_of_not_gt hSpos) hSnonneg
    constructor <;> dsimp [S] at hSz <;>
      nlinarith [sq_nonneg dx, sq_nonneg dy]

end CP15
