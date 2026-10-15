import CP15.K10ModelCover
import CP15.AlternatingGeometry

namespace CP15

/-- This one additional rational angle item bounds the actual outer
separation angle; it is not inferred from observed boundary gaps. -/
theorem k10_outer_alpha_scalar_checked :
    scalarAngleCheck (3521357 / 1000000) (3521357 / 1000000) 57588 100000 = true := by
  decide +kernel

theorem k10_outerAlpha_lower (b : ℝ) (hb : 3 < b) (hbC : b ≤ candidateB) :
    (57588 / 100000 : ℝ) ≤ outerAlpha b := by
  have hh := scalarAngleCheck_sound (3521357 / 1000000) (3521357 / 1000000)
    57588 100000 k10_outer_alpha_scalar_checked (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at hh
  rw [contactAngle_diagonal_eq_outerAlpha _ (by norm_num)] at hh
  have hm := outerAlpha_antitone_radius b (3521357 / 1000000)
    (by linarith) (hbC.trans Candidate.candidateB_lt_3521357_div_1000000.le)
  nlinarith

theorem k10_turn_upper : 100000 * (2 * Real.pi) ≤ (628319 : ℝ) := by
  linarith [Real.pi_lt_d6]

end CP15
