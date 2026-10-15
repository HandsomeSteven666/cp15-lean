import CP15.K9ScalarBounds

namespace CP15

/-- The cubic sine remainder used in the existing K9 scalar certificate
also controls cosine through two radians: only the half angle must be at
most one. -/
theorem cos_lower_from_sin_cubic_two (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) :
    1 - 2 * sinCubicUpper (θ / 2) ^ 2 ≤ Real.cos θ := by
  let x := θ / 2
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0
      (by linarith [Real.pi_gt_three])
  have hbound := Real.sin_bound
    (x := x) (by simpa [abs_of_nonneg hx0] using hx1)
  have hsinupper : Real.sin x ≤ sinCubicUpper x := by
    have h := (abs_le.mp hbound).2
    rw [abs_of_nonneg hx0] at h
    dsimp [sinCubicUpper]
    linarith
  have hpoly0 : 0 ≤ sinCubicUpper x := le_trans hsin0 hsinupper
  have hsq : Real.sin x ^ 2 ≤ sinCubicUpper x ^ 2 := by
    nlinarith [mul_nonneg hsin0 (sub_nonneg.mpr hsinupper),
      mul_nonneg hpoly0 (sub_nonneg.mpr hsinupper)]
  have hcosid : Real.cos θ = 1 - 2 * Real.sin x ^ 2 := by
    have htwo := Real.cos_two_mul x
    have hsumsq := Real.sin_sq_add_cos_sq x
    have hdouble : 2 * x = θ := by dsimp [x]; ring
    rw [hdouble] at htwo
    nlinarith
  rw [hcosid]
  dsimp [x] at hsq ⊢
  linarith

/-- A fully rational half-angle enclosure turns the existing exact
sine remainder into a strict cosine lower bound. -/
theorem cos_gt_of_half_interval
    (θ l u c : ℝ)
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hl0 : 0 ≤ l) (hlx : l ≤ θ / 2)
    (hxu : θ / 2 ≤ u) (hu1 : u ≤ 1)
    (hcert : c < 1 - 2 *
      (u - l ^ 3 / 6 + u ^ 5 / 100) ^ 2) :
    c < Real.cos θ := by
  let x := θ / 2
  let U := u - l ^ 3 / 6 + u ^ 5 / 100
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hx3 : l ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hl0 hlx 3
  have hx5 : x ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ hx0 hxu 5
  have hPU : sinCubicUpper x ≤ U := by
    dsimp [sinCubicUpper, U, x] at *
    linarith
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0
      (by linarith [Real.pi_gt_three])
  have hbound := Real.sin_bound
    (x := x) (by simpa [abs_of_nonneg hx0] using hx1)
  have hsinupper : Real.sin x ≤ sinCubicUpper x := by
    have h := (abs_le.mp hbound).2
    rw [abs_of_nonneg hx0] at h
    dsimp [sinCubicUpper]
    linarith
  have hP0 : 0 ≤ sinCubicUpper x := le_trans hsin0 hsinupper
  have hU0 : 0 ≤ U := hP0.trans hPU
  have hsq : sinCubicUpper x ^ 2 ≤ U ^ 2 := by
    nlinarith [mul_nonneg hP0 (sub_nonneg.mpr hPU),
      mul_nonneg hU0 (sub_nonneg.mpr hPU)]
  have hcos := cos_lower_from_sin_cubic_two θ hθ0 hθ2
  dsimp [x] at hsq
  dsimp [U] at hsq hcert
  linarith

/-- The tight shared-branch `A-H` threshold, 49.2 degrees. -/
theorem cos_41pi_div_150_gt_653377ppm :
    (653377 / 1000000 : ℝ) <
      Real.cos (41 * Real.pi / 150) := by
  let l : ℝ := 41 * (3141592 / 1000000) / 300
  let u : ℝ := 41 * (3141593 / 1000000) / 300
  have hθ0 : (0 : ℝ) ≤ 41 * Real.pi / 150 := by
    positivity
  have hθ2 : 41 * Real.pi / 150 ≤ (2 : ℝ) := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (41 * Real.pi / 150) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (41 * Real.pi / 150) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

/-- The final shared-branch angle tests. -/
theorem cos_607pi_div_1800_gt_489permille :
    (489 / 1000 : ℝ) <
      Real.cos (607 * Real.pi / 1800) := by
  let l : ℝ := 607 * (3141592 / 1000000) / 3600
  let u : ℝ := 607 * (3141593 / 1000000) / 3600
  have hθ0 : (0 : ℝ) ≤ 607 * Real.pi / 1800 := by positivity
  have hθ2 : 607 * Real.pi / 1800 ≤ (2 : ℝ) := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (607 * Real.pi / 1800) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (607 * Real.pi / 1800) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

theorem cos_23pi_div_75_gt_5705ppm :
    (5705 / 10000 : ℝ) <
      Real.cos (23 * Real.pi / 75) := by
  let l : ℝ := 23 * (3141592 / 1000000) / 150
  let u : ℝ := 23 * (3141593 / 1000000) / 150
  have hθ0 : (0 : ℝ) ≤ 23 * Real.pi / 75 := by positivity
  have hθ2 : 23 * Real.pi / 75 ≤ (2 : ℝ) := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (23 * Real.pi / 75) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (23 * Real.pi / 75) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

theorem cos_59pi_div_150_gt_328permille :
    (328 / 1000 : ℝ) <
      Real.cos (59 * Real.pi / 150) := by
  let l : ℝ := 59 * (3141592 / 1000000) / 300
  let u : ℝ := 59 * (3141593 / 1000000) / 300
  have hθ0 : (0 : ℝ) ≤ 59 * Real.pi / 150 := by positivity
  have hθ2 : 59 * Real.pi / 150 ≤ (2 : ℝ) := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (59 * Real.pi / 150) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (59 * Real.pi / 150) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

theorem cos_53pi_div_180_gt_601permille :
    (601 / 1000 : ℝ) <
      Real.cos (53 * Real.pi / 180) := by
  let l : ℝ := 53 * (3141592 / 1000000) / 360
  let u : ℝ := 53 * (3141593 / 1000000) / 360
  have hθ0 : (0 : ℝ) ≤ 53 * Real.pi / 180 := by positivity
  have hθ2 : 53 * Real.pi / 180 ≤ (2 : ℝ) := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (53 * Real.pi / 180) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (53 * Real.pi / 180) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

theorem cos_11pi_div_20_gt_neg_16permille :
    (-16 / 100 : ℝ) <
      Real.cos (11 * Real.pi / 20) := by
  let l : ℝ := 11 * (3141592 / 1000000) / 40
  let u : ℝ := 11 * (3141593 / 1000000) / 40
  have hθ0 : (0 : ℝ) ≤ 11 * Real.pi / 20 := by positivity
  have hθ2 : 11 * Real.pi / 20 ≤ (2 : ℝ) := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (11 * Real.pi / 20) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (11 * Real.pi / 20) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

end CP15
