import CP15.M3K9

open scoped InnerProductSpace

namespace CP15

/-- The selected non-outer radial cap is below a simple rational number
uniformly for every radius no larger than the candidate. -/
theorem F_lt_1301_div_1000_of_le_candidateB (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) :
    F b < 1301 / 1000 := by
  have hBq : b ≤ (352136 / 100000 : ℝ) :=
    (hbB.trans_lt Candidate.candidateB_lt_352136_div_100000).le
  have hBpos : (0 : ℝ) < 352136 / 100000 := by norm_num
  have hrec : 4 / (352136 / 100000 : ℝ) ≤ 4 / b := by
    apply (div_le_div_iff₀ hBpos (by linarith)).2
    nlinarith [hBq]
  have hDbupper : D b < (238544 / 100000 : ℝ) := by
    have hcorner : (352136 / 100000 : ℝ) -
        4 / (352136 / 100000 : ℝ) < 238544 / 100000 := by norm_num
    unfold D
    linarith
  have hDpos : 0 < D b := D_pos hb
  by_cases hrad : 0 ≤ D b ^ 2 - 4
  · have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
      unfold F
      exact Real.sq_sqrt hrad
    have hFn : 0 ≤ F b := by unfold F; exact Real.sqrt_nonneg _
    nlinarith
  · have hzero : F b = 0 := by
      unfold F
      exact Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hrad)
    rw [hzero]
    norm_num

/-- Three separated centers in a disk of radius `1301/1000` all have
radius strictly above `4/5`. The proof uses only a vector-sum bound and
Cauchy–Schwarz, without polar angles or planar ordering. -/
theorem three_separated_small_centers_radius_gt_four_fifths
    (x y z : Plane)
    (hx : ‖x‖ ≤ 1301 / 1000)
    (hy : ‖y‖ ≤ 1301 / 1000)
    (hz : ‖z‖ ≤ 1301 / 1000)
    (hxy : 2 ≤ dist x y)
    (hxz : 2 ≤ dist x z)
    (hyz : 2 ≤ dist y z) : (4 / 5 : ℝ) < ‖x‖ := by
  by_contra hnot
  have hxsmall : ‖x‖ ≤ (4 / 5 : ℝ) := le_of_not_gt hnot
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  have hz0 := norm_nonneg z
  have hxy2 : 4 ≤ dist x y ^ 2 := by nlinarith [dist_nonneg (x := x) (y := y)]
  have hxz2 : 4 ≤ dist x z ^ 2 := by nlinarith [dist_nonneg (x := x) (y := z)]
  have hyz2 : 4 ≤ dist y z ^ 2 := by nlinarith [dist_nonneg (x := y) (y := z)]
  rw [dist_eq_norm, norm_sub_sq_real] at hxy2 hxz2 hyz2
  have hdot : ⟪x, y + z⟫_ℝ ≤ ‖x‖ ^ 2 + (1301 / 1000 : ℝ) ^ 2 - 4 := by
    rw [inner_add_right]
    nlinarith [sq_nonneg (‖y‖ - 1301 / 1000),
      sq_nonneg (‖z‖ - 1301 / 1000)]
  have hsum : ‖y + z‖ ^ 2 ≤ 4 * (1301 / 1000 : ℝ) ^ 2 - 4 := by
    rw [norm_add_sq_real]
    nlinarith [hyz2, sq_nonneg (‖y‖ - 1301 / 1000),
      sq_nonneg (‖z‖ - 1301 / 1000)]
  have hdotneg : ⟪x, y + z⟫_ℝ < -(3 / 2 : ℝ) := by
    nlinarith
  have hcs := abs_real_inner_le_norm x (y + z)
  have hsqcs : ⟪x, y + z⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖y + z‖ ^ 2 := by
    have habs := abs_nonneg (⟪x, y + z⟫_ℝ)
    have hprod := mul_nonneg hx0 (norm_nonneg (y + z))
    nlinarith [sq_abs (⟪x, y + z⟫_ℝ)]
  have hxyprod := mul_le_mul_of_nonneg_left hsum (sq_nonneg ‖x‖)
  nlinarith [hsqcs, hxyprod]

/-- Uniform polynomial cosine bound for a non-outer center and a
touching-inner center. The two radial variables are bounded by exact
rational caps; no numerical optimizer is used. -/
theorem low_high_pair_cos_poly_lt
    (r s : ℝ)
    (hrlo : (4 / 5 : ℝ) ≤ r) (hrhi : r ≤ 1301 / 1000)
    (hslo : (7 / 5 : ℝ) ≤ s) (hshi : s ≤ 14909 / 6250) :
    r ^ 2 + s ^ 2 - 4 < 2 * (615 / 1000 : ℝ) * r * s := by
  let U : ℝ := 14909 / 6250
  let c : ℝ := 615 / 1000
  have hfactor_s : 0 ≤ (U - s) * (U + s - 2 * c * r) := by
    apply mul_nonneg (by dsimp [U]; linarith)
    dsimp [U, c]
    nlinarith
  have hfactor_r : 0 ≤ (r - 4 / 5) *
      (2 * c * U - r - 4 / 5) := by
    apply mul_nonneg (by linarith)
    dsimp [U, c]
    nlinarith
  have hcorner : (4 / 5 : ℝ) ^ 2 + U ^ 2 - 4 <
      2 * c * (4 / 5) * U := by
    dsimp [U, c]
    norm_num
  dsimp [U, c] at *
  nlinarith [hfactor_s, hfactor_r, hcorner]

/-- Uniform polynomial cosine bound for two touching-inner centers. -/
theorem high_high_pair_cos_poly_lt
    (r s : ℝ)
    (hrlo : (7 / 5 : ℝ) ≤ r) (hrhi : r ≤ 14909 / 6250)
    (hslo : (7 / 5 : ℝ) ≤ s) (hshi : s ≤ 14909 / 6250) :
    r ^ 2 + s ^ 2 - 4 < 2 * (65 / 100 : ℝ) * r * s := by
  let U : ℝ := 14909 / 6250
  let c : ℝ := 65 / 100
  have hfactor_r : 0 ≤ (U - r) * (U + r - 2 * c * s) := by
    apply mul_nonneg (by dsimp [U]; linarith)
    dsimp [U, c]
    nlinarith
  have hfactor_s : 0 ≤ (U - s) * (U + s - 2 * c * U) := by
    apply mul_nonneg (by dsimp [U]; linarith)
    dsimp [U, c]
    nlinarith
  have hcorner : U ^ 2 + U ^ 2 - 4 < 2 * c * U * U := by
    dsimp [U, c]
    norm_num
  dsimp [U, c] at *
  nlinarith [hfactor_r, hfactor_s, hcorner]

theorem cos_181_div_200_gt_615_div_1000 :
    (615 / 1000 : ℝ) < Real.cos (181 / 200 : ℝ) := by
  have h := cos_lower_from_sin_cubic (181 / 200 : ℝ)
    (by norm_num) (by norm_num)
  have hrat : (615 / 1000 : ℝ) <
      1 - 2 * sinCubicUpper ((181 / 200 : ℝ) / 2) ^ 2 := by
    norm_num [sinCubicUpper]
  linarith

theorem cos_171_div_200_gt_65_div_100 :
    (65 / 100 : ℝ) < Real.cos (171 / 200 : ℝ) := by
  have h := cos_lower_from_sin_cubic (171 / 200 : ℝ)
    (by norm_num) (by norm_num)
  have hrat : (65 / 100 : ℝ) <
      1 - 2 * sinCubicUpper ((171 / 200 : ℝ) / 2) ^ 2 := by
    norm_num [sinCubicUpper]
  linarith

/-- Pairwise distance and a polynomial cosine bound imply a strict
separation of any chosen short polar-angle lift. -/
theorem polar_pair_angle_gt_of_poly
    (x y : Plane) (g c θ : ℝ)
    (hrx : 0 < ‖x‖) (hry : 0 < ‖y‖)
    (hsep : 2 ≤ dist x y)
    (hpoly : ‖x‖ ^ 2 + ‖y‖ ^ 2 - 4 < 2 * c * ‖x‖ * ‖y‖)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hcθ : c < Real.cos θ) : θ < g := by
  have hdist2 : 4 ≤ dist x y ^ 2 := by nlinarith [dist_nonneg (x := x) (y := y)]
  rw [dist_eq_norm, norm_sub_sq_real] at hdist2
  have hpolar := polar_inner x y
  rw [hcoslift] at hpolar
  have hcos : Real.cos g < c := by
    nlinarith [mul_pos hrx hry]
  by_contra hnot
  have hgθ : g ≤ θ := le_of_not_gt hnot
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hg0 hθpi hgθ
  linarith

theorem low_low_angle_gt_pi_div_two
    (x y : Plane) (g : ℝ)
    (hx0 : 0 < ‖x‖) (hy0 : 0 < ‖y‖)
    (hx : ‖x‖ ≤ 1301 / 1000) (hy : ‖y‖ ≤ 1301 / 1000)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    Real.pi / 2 < g := by
  have hpoly : ‖x‖ ^ 2 + ‖y‖ ^ 2 - 4 <
      2 * (-1 / 100 : ℝ) * ‖x‖ * ‖y‖ := by
    nlinarith
  exact polar_pair_angle_gt_of_poly x y g (-1 / 100) (Real.pi / 2)
    hx0 hy0 hsep hpoly hcoslift hg0 hgpi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by rw [Real.cos_pi_div_two]; norm_num)

theorem low_high_angle_gt_181_div_200
    (x y : Plane) (g : ℝ)
    (hxlo : (4 / 5 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 14909 / 6250)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    (181 / 200 : ℝ) < g := by
  exact polar_pair_angle_gt_of_poly x y g (615 / 1000) (181 / 200)
    (by linarith) (by linarith) hsep
    (low_high_pair_cos_poly_lt ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by norm_num)
    (by linarith [Real.pi_gt_three])
    cos_181_div_200_gt_615_div_1000

theorem high_high_angle_gt_171_div_200
    (x y : Plane) (g : ℝ)
    (hxlo : (7 / 5 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 14909 / 6250)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 14909 / 6250)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    (171 / 200 : ℝ) < g := by
  exact polar_pair_angle_gt_of_poly x y g (65 / 100) (171 / 200)
    (by linarith) (by linarith) hsep
    (high_high_pair_cos_poly_lt ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by norm_num)
    (by linarith [Real.pi_gt_three])
    cos_171_div_200_gt_65_div_100

end CP15
