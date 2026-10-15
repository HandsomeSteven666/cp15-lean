import CP15.CandidateBounds

namespace CP15

/-- Minimal polar separation of two radius-`b` points at distance two. -/
noncomputable def outerAlpha (b : ℝ) : ℝ :=
  2 * Real.arcsin (1 / b)

/-- The elementary bound `arcsin x ≥ x` on `[0,1]`, specialized to a
positive outer radius. -/
theorem outerAlpha_ge_two_div (b : ℝ) (hb : 1 ≤ b) :
    2 / b ≤ outerAlpha b := by
  have hbpos : 0 < b := by linarith
  have hx0 : 0 ≤ 1 / b := by positivity
  have hx1 : 1 / b ≤ 1 := (div_le_iff₀ hbpos).2 (by linarith)
  have ha0 : 0 ≤ Real.arcsin (1 / b) := by
    simpa [Real.arcsin_zero] using Real.arcsin_le_arcsin hx0
  have hsin : Real.sin (Real.arcsin (1 / b)) = 1 / b :=
    Real.sin_arcsin (by linarith) hx1
  have hle := Real.sin_le ha0
  rw [hsin] at hle
  simpa [outerAlpha, div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)

/-- A rational enclosure of the candidate radius gives the strict
eight-gap inequality without numerical inverse-trigonometric evaluation. -/
theorem eight_outerAlpha_gt_pi (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) :
    Real.pi < 8 * outerAlpha b := by
  have hbq : b < 353 / 100 :=
    hbB.trans_lt Candidate.candidateB_lt_353_div_100
  have hfrac : 4 < 16 / b := by
    apply (lt_div_iff₀ (by linarith : 0 < b)).2
    nlinarith
  have ha := outerAlpha_ge_two_div b (by linarith)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hprod : 16 / b ≤ 8 * outerAlpha b := by
    calc
      16 / b = 8 * (2 / b) := by ring
      _ ≤ 8 * outerAlpha b :=
        mul_le_mul_of_nonneg_left ha (by norm_num)
  linarith

end CP15
