import CP15.Definitions

open scoped InnerProductSpace

namespace CP15

/-- A contact beyond the radial tangent hyperplane has strictly larger
squared radius by more than the squared contact length. -/
theorem blocker_radius_sq (x y : Plane)
    (hcontact : dist x y = 2)
    (hblock : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ) :
    ‖x‖ ^ 2 + 4 < ‖y‖ ^ 2 := by
  have hsq : ‖y - x‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, dist_comm, hcontact]
    norm_num
  rw [norm_sub_sq_real] at hsq
  nlinarith

/-- Squared-distance expansion for a positive radial move without division
by the center radius. -/
theorem radial_move_sq (x y : Plane) (t : ℝ) (ht : 0 ≤ t) :
    ‖(1 + t) • x - y‖ ^ 2 =
      ‖x - y‖ ^ 2 + 2 * t * (‖x‖ ^ 2 - ⟪y, x⟫_ℝ) +
        t ^ 2 * ‖x‖ ^ 2 := by
  have ht1 : 0 ≤ 1 + t := by linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht1, real_inner_smul_left]
  rw [real_inner_comm y x]
  ring

/-- Replacing a maximally radial inner point by the corresponding boundary
point increases its squared distance to every point of no larger radius. -/
theorem radial_replace_inner_distance
    (u y : Plane) (r b : ℝ)
    (hr : 0 ≤ r) (hbr : r < b)
    (hu : ‖u‖ = 1) (hy : ‖y‖ ≤ r) :
    ‖b • u - y‖ ^ 2 - ‖r • u - y‖ ^ 2 ≥ (b - r) ^ 2 := by
  have hb : 0 ≤ b := le_trans hr hbr.le
  have hdot : ⟪u, y⟫_ℝ ≤ r := by
    calc
      ⟪u, y⟫_ℝ ≤ ‖u‖ * ‖y‖ := real_inner_le_norm u y
      _ = ‖y‖ := by rw [hu]; ring
      _ ≤ r := hy
  have hq : ‖b • u - y‖ ^ 2 = b ^ 2 - 2 * b * ⟪u, y⟫_ℝ + ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hb, hu, real_inner_smul_left]
    ring
  have hx : ‖r • u - y‖ ^ 2 = r ^ 2 - 2 * r * ⟪u, y⟫_ℝ + ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr, hu, real_inner_smul_left]
    ring
  have hnonneg : 0 ≤ (b - r) * (r - ⟪u, y⟫_ℝ) :=
    mul_nonneg (sub_nonneg.mpr hbr.le) (sub_nonneg.mpr hdot)
  rw [hq, hx]
  nlinarith

noncomputable def D (b : ℝ) : ℝ := b - 4 / b

/-- Exact outer-point comparison, including the endpoint `r = D b`. -/
theorem radial_replace_outer_distance
    (u z : Plane) (r b : ℝ)
    (hr : 0 < r) (hbr : r < b)
    (hu : ‖u‖ = 1) (hz : ‖z‖ = b)
    (hsep : 2 ≤ dist (r • u) z) :
    b * (b - r) * (r - D b) / r ≤ ‖b • u - z‖ ^ 2 - 4 := by
  have hb : 0 < b := hr.trans hbr
  let a : ℝ := ⟪u, z⟫_ℝ
  have hx : ‖r • u - z‖ ^ 2 = r ^ 2 - 2 * r * a + b ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.le, hu, hz, real_inner_smul_left]
    ring
  have hq : ‖b • u - z‖ ^ 2 = 2 * b ^ 2 - 2 * b * a := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hb.le, hu, hz, real_inner_smul_left]
    ring
  have hsep2 : 4 ≤ r ^ 2 - 2 * r * a + b ^ 2 := by
    have hsq : 4 ≤ dist (r • u) z ^ 2 := by
      have hn : 0 ≤ dist (r • u) z := dist_nonneg
      nlinarith
    rw [dist_eq_norm, hx] at hsq
    exact hsq
  have hpositive : 0 ≤ b * (r ^ 2 - 2 * r * a + b ^ 2 - 4) :=
    mul_nonneg hb.le (sub_nonneg.mpr hsep2)
  have hid :
      r * ((2 * b ^ 2 - 2 * b * a - 4) -
        b * (b - r) * (r - D b) / r) =
      b * (r ^ 2 - 2 * r * a + b ^ 2 - 4) := by
    dsimp [D]
    field_simp
    ring
  rw [hq]
  by_contra hnot
  have hneg : (2 * b ^ 2 - 2 * b * a - 4) -
      b * (b - r) * (r - D b) / r < 0 := by linarith
  have hmul := mul_neg_of_pos_of_neg hr hneg
  rw [hid] at hmul
  linarith

theorem radial_replace_inner_separated
    (u y : Plane) (r b : ℝ)
    (hr : 0 ≤ r) (hbr : r < b)
    (hu : ‖u‖ = 1) (hy : ‖y‖ ≤ r)
    (hsep : 2 ≤ dist (r • u) y) :
    2 ≤ dist (b • u) y := by
  have hgain := radial_replace_inner_distance u y r b hr hbr hu hy
  rw [dist_eq_norm] at hsep ⊢
  have hnonneg : 0 ≤ ‖b • u - y‖ := norm_nonneg _
  nlinarith [sq_nonneg (b - r)]

theorem radial_replace_outer_separated
    (u z : Plane) (r b : ℝ)
    (hr : 0 < r) (hbr : r < b)
    (hu : ‖u‖ = 1) (hz : ‖z‖ = b)
    (hD : D b ≤ r)
    (hsep : 2 ≤ dist (r • u) z) :
    2 ≤ dist (b • u) z := by
  have hgain := radial_replace_outer_distance u z r b hr hbr hu hz hsep
  have hb : 0 ≤ b := (hr.trans hbr).le
  have hnonneg : 0 ≤ b * (b - r) * (r - D b) / r := by positivity
  have hsq : 4 ≤ ‖b • u - z‖ ^ 2 := by linarith
  rw [dist_eq_norm]
  have hn : 0 ≤ ‖b • u - z‖ := norm_nonneg _
  nlinarith

end CP15
