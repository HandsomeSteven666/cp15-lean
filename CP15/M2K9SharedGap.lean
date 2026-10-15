import CP15.M2K9ClassWords

namespace CP15

/-- The exact six-gap arithmetic at scale ten tenths per degree. The
premises deliberately expose every geometric angle estimate; a proof
that actual polar gaps satisfy them is a separate obligation. -/
theorem shared_six_gap_budget_impossible
    (g₀ g₁ g₂ g₃ g₄ g₅ : ℝ)
    (hsum : g₀ + g₁ + g₂ + g₃ + g₄ + g₅ = 3600)
    (homega : 1133 < g₀ + g₅)
    (hpattern :
      (708 < g₁ ∧ 552 < g₂ ∧ 552 < g₃ ∧ 708 < g₄) ∨
      (607 < g₁ ∧ 552 < g₂ ∧ 600 ≤ g₃ ∧ 708 < g₄) ∨
      (708 < g₁ ∧ 600 ≤ g₂ ∧ 552 < g₃ ∧ 607 < g₄)) :
    False := by
  rcases hpattern with hmid | hleft | hright
  · rcases hmid with ⟨h₁, h₂, h₃, h₄⟩
    linarith
  · rcases hleft with ⟨h₁, h₂, h₃, h₄⟩
    linarith
  · rcases hright with ⟨h₁, h₂, h₃, h₄⟩
    linarith

/-- The exact radian form of the six-gap contradiction. The combined
offset threshold is `1133*pi/1800`; all pairwise thresholds are rational
multiples of pi, so the endpoint cases close at equality before strictness. -/
theorem shared_six_gap_radian_budget_impossible
    (g₀ g₁ g₂ g₃ g₄ g₅ : ℝ)
    (hsum : g₀ + g₁ + g₂ + g₃ + g₄ + g₅ = 2 * Real.pi)
    (homega : 1133 * Real.pi / 1800 < g₀ + g₅)
    (hpattern :
      ((59 * Real.pi / 150 < g₁) ∧
        (23 * Real.pi / 75 < g₂) ∧
        (23 * Real.pi / 75 < g₃) ∧
        (59 * Real.pi / 150 < g₄)) ∨
      ((607 * Real.pi / 1800 < g₁) ∧
        (23 * Real.pi / 75 < g₂) ∧
        (Real.pi / 3 ≤ g₃) ∧
        (59 * Real.pi / 150 < g₄)) ∨
      ((59 * Real.pi / 150 < g₁) ∧
        (Real.pi / 3 ≤ g₂) ∧
        (23 * Real.pi / 75 < g₃) ∧
        (607 * Real.pi / 1800 < g₄))) : False := by
  rcases hpattern with hmid | hleft | hright
  · rcases hmid with ⟨h₁, h₂, h₃, h₄⟩
    have hpi := Real.pi_pos
    linarith
  · rcases hleft with ⟨h₁, h₂, h₃, h₄⟩
    have hpi := Real.pi_pos
    linarith
  · rcases hright with ⟨h₁, h₂, h₃, h₄⟩
    have hpi := Real.pi_pos
    linarith

end CP15
