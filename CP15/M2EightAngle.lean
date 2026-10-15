import CP15.M2K10

namespace CP15

/-- A low center in the two-nonouter case may be as close as `699/1000`
to the origin. This rational corner still gives a usable angular bound
against every touching-inner center. -/
theorem m2_low_high_cos_poly_lt (r s : ℝ)
    (hrlo : (699 / 1000 : ℝ) ≤ r) (hrhi : r ≤ 1301 / 1000)
    (hslo : (7 / 5 : ℝ) ≤ s) (hshi : s ≤ 14909 / 6250) :
    r ^ 2 + s ^ 2 - 4 < 2 * (7 / 10 : ℝ) * r * s := by
  let U : ℝ := 14909 / 6250
  let c : ℝ := 7 / 10
  let L : ℝ := 699 / 1000
  have hfactor_s : 0 ≤ (U - s) * (U + s - 2 * c * r) := by
    apply mul_nonneg (by dsimp [U]; linarith)
    dsimp [U, c]
    nlinarith
  have hfactor_r : 0 ≤ (r - L) * (2 * c * U - r - L) := by
    apply mul_nonneg (by dsimp [L]; linarith)
    dsimp [U, c, L]
    nlinarith
  have hcorner : L ^ 2 + U ^ 2 - 4 < 2 * c * L * U := by
    dsimp [U, c, L]
    norm_num
  dsimp [U, c, L] at *
  nlinarith [hfactor_s, hfactor_r, hcorner]

theorem m2_cos_three_fourths_gt_seven_tenths :
    (7 / 10 : ℝ) < Real.cos (3 / 4 : ℝ) := by
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := (3 / 4 : ℝ))]

theorem m2_low_high_angle_gt_three_fourths
    (x y : Plane) (g : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 14909 / 6250)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    (3 / 4 : ℝ) < g := by
  exact polar_pair_angle_gt_of_poly x y g (7 / 10) (3 / 4)
    (by linarith) (by linarith) hsep
    (m2_low_high_cos_poly_lt ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by norm_num)
    (by linarith [Real.pi_gt_three])
    m2_cos_three_fourths_gt_seven_tenths

def eightAngleWeight (color : Fin 8 → Bool) (i : Fin 8) : ℚ :=
  if color i then
    if color (i + 1) then 3 / 2 else 3 / 4
  else if color (i + 1) then 3 / 4 else 171 / 200

/-- Complete 256-word finite check, with exactly two low-radius labels.
No symmetry quotient or external enumeration is trusted. -/
theorem eightAngleWeight_sum_ge :
    ∀ color : Fin 8 → Bool,
      (Finset.univ.filter (fun i => color i)).card = 2 →
      (321 / 50 : ℚ) ≤ ∑ i : Fin 8, eightAngleWeight color i := by
  decide +kernel

theorem eight_polarArg_injective
    (q : Fin 8 → Plane) (hsep : Separated q 2)
    (hrlo : ∀ i, (699 / 1000 : ℝ) ≤ ‖q i‖)
    (hrhi : ∀ i, ‖q i‖ ≤ 14909 / 6250) :
    Function.Injective (fun i => polarArg (q i)) := by
  intro i j harg
  by_contra hij
  have hd := hsep i j hij
  have hd2 : 4 ≤ dist (q i) (q j) ^ 2 := by
    nlinarith [dist_nonneg (x := q i) (y := q j)]
  rw [dist_eq_norm, norm_sub_sq_real] at hd2
  have hdot := polar_inner (q i) (q j)
  change polarArg (q i) = polarArg (q j) at harg
  rw [harg, sub_self, Real.cos_zero] at hdot
  have hloi := hrlo i
  have hloj := hrlo j
  have hhii := hrhi i
  have hhij := hrhi j
  nlinarith

end CP15
