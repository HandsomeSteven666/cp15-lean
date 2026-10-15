import CP15.M2KLow

namespace CP15

/-- Rational cyclic gap demand for five high centers and two labeled low
centers. The two low labels can have different certified angle bounds. -/
noncomputable def sevenTwoLowWeight (pos0 pos1 : Fin 7) (q0 q1 : ℝ)
    (i : Fin 7) : ℝ :=
  if i = pos0 then
    if i + 1 = pos1 then 3 / 2 else q0
  else if i = pos1 then
    if i + 1 = pos0 then 3 / 2 else q1
  else if i + 1 = pos0 then q0
  else if i + 1 = pos1 then q1
  else 431 / 500

set_option maxHeartbeats 0

/-- Complete 42-position cyclic check. The only analytic input is the
combined lower angle budget of the two low centers. -/
theorem sevenTwoLowWeight_sum_ge
    (q0 q1 : ℝ)
    (h0 : 0 ≤ q0) (h1 : 0 ≤ q1)
    (hsum : (1851 / 1000 : ℝ) ≤ q0 + q1)
    (pos0 pos1 : Fin 7) (hne : pos0 ≠ pos1) :
    (6287 / 1000 : ℝ) ≤
      ∑ i : Fin 7, sevenTwoLowWeight pos0 pos1 q0 q1 i := by
  fin_cases pos0 <;> fin_cases pos1 <;>
    simp_all [Fin.sum_univ_seven, sevenTwoLowWeight] <;> linarith

def m2CellA (k : Fin 8) : ℚ :=
  (2796 + 301 * k.val) / 4000

def m2CellQ : Fin 8 → ℚ
  | 0 => 858 / 1000
  | 1 => 902 / 1000
  | 2 => 933 / 1000
  | 3 => 955 / 1000
  | 4 => 971 / 1000
  | 5 => 982 / 1000
  | 6 => 989 / 1000
  | 7 => 993 / 1000

def m2CellC : Fin 8 → ℚ
  | 0 => 65339 / 100000
  | 1 => 6199 / 10000
  | 2 => 59513 / 100000
  | 3 => 57697 / 100000
  | 4 => 56391 / 100000
  | 5 => 55489 / 100000
  | 6 => 54911 / 100000
  | 7 => 27299 / 50000

theorem m2_cell_rational_conditions (k : Fin 8) :
    (699 / 1000 : ℝ) ≤ m2CellA k ∧
    2 * (m2CellC k : ℝ) * (1301 / 1000) ≤
      14909 / 6250 + 7 / 5 ∧
    1301 / 1000 + (m2CellA k : ℝ) ≤
      2 * (m2CellC k : ℝ) * (14909 / 6250) ∧
    (m2CellA k : ℝ) ^ 2 + (14909 / 6250) ^ 2 - 4 <
      2 * (m2CellC k : ℝ) * (m2CellA k : ℝ) *
        (14909 / 6250) ∧
    (m2CellC k : ℝ) <
      1 - 2 * sinCubicUpper ((m2CellQ k : ℝ) / 2) ^ 2 ∧
    0 ≤ (m2CellQ k : ℝ) ∧ (m2CellQ k : ℝ) ≤ 1 := by
  fin_cases k <;> norm_num [m2CellA, m2CellQ, m2CellC,
    sinCubicUpper]

/-- A radius-dependent low-to-high angle bound at eight exact rational
lower-radius corners. Every polynomial and cosine enclosure is checked
inside Lean. -/
theorem m2_low_high_angle_gt_cell
    (k : Fin 8) (x y : Plane) (g : ℝ)
    (hxlo : (m2CellA k : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 14909 / 6250)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    (m2CellQ k : ℝ) < g := by
  let U : ℝ := 14909 / 6250
  let c : ℝ := m2CellC k
  let L : ℝ := m2CellA k
  have hc := m2_cell_rational_conditions k
  have hfactor_s : 0 ≤ (U - ‖y‖) * (U + ‖y‖ - 2 * c * ‖x‖) := by
    apply mul_nonneg (by dsimp [U]; linarith)
    dsimp [U, c]
    nlinarith [hc.2.1]
  have hfactor_r : 0 ≤ (‖x‖ - L) * (2 * c * U - ‖x‖ - L) := by
    apply mul_nonneg (by dsimp [L]; linarith)
    dsimp [U, c, L]
    nlinarith [hc.2.2.1]
  have hpoly : ‖x‖ ^ 2 + ‖y‖ ^ 2 - 4 <
      2 * c * ‖x‖ * ‖y‖ := by
    dsimp [U, c, L] at *
    nlinarith [hfactor_s, hfactor_r, hc.2.2.2.1]
  have hcoslower := cos_lower_from_sin_cubic (m2CellQ k : ℝ)
    hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  have hcos : c < Real.cos (m2CellQ k : ℝ) := by
    dsimp [c]
    linarith [hc.2.2.2.2.1]
  exact polar_pair_angle_gt_of_poly x y g c (m2CellQ k : ℝ)
    (by linarith [hc.1]) (by linarith) hsep hpoly
    hcoslift hg0 hgpi hc.2.2.2.2.2.1
    (by linarith [Real.pi_gt_three]) hcos

/-- The eight closed radial cells cover every permitted low-radius pair.
The second lower endpoint is forced by `r₀+r₁≥2`. -/
theorem m2_pair_eight_cell_cover
    (r₀ r₁ : ℝ)
    (hlo : (699 / 1000 : ℝ) ≤ r₀)
    (hhi : r₀ ≤ 1301 / 1000)
    (hsum : 2 ≤ r₀ + r₁) :
    ∃ k : Fin 8,
      (m2CellA k : ℝ) ≤ r₀ ∧
      (m2CellA ⟨7 - k.val, by omega⟩ : ℝ) ≤ r₁ ∧
      (1851 / 1000 : ℝ) ≤
        (m2CellQ k : ℝ) +
          (m2CellQ ⟨7 - k.val, by omega⟩ : ℝ) := by
  by_cases h₀ : r₀ ≤ (m2CellA 1 : ℝ)
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith
  by_cases h₁ : r₀ ≤ (m2CellA 2 : ℝ)
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith
  by_cases h₂ : r₀ ≤ (m2CellA 3 : ℝ)
  · refine ⟨2, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith
  by_cases h₃ : r₀ ≤ (m2CellA 4 : ℝ)
  · refine ⟨3, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith
  by_cases h₄ : r₀ ≤ (m2CellA 5 : ℝ)
  · refine ⟨4, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith
  by_cases h₅ : r₀ ≤ (m2CellA 6 : ℝ)
  · refine ⟨5, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith
  by_cases h₆ : r₀ ≤ (m2CellA 7 : ℝ)
  · refine ⟨6, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith
  refine ⟨7, ?_, ?_, ?_⟩ <;> norm_num [m2CellA, m2CellQ] at * <;> linarith

end CP15
