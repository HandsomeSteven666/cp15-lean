import CP15.Definitions

open scoped InnerProductSpace

namespace CP15

private def dot2 (x y : Plane) : ℝ :=
  x 0 * y 0 + x 1 * y 1

private def cross2 (x y : Plane) : ℝ :=
  x 0 * y 1 - x 1 * y 0

private theorem norm_sq_eq_dot2 (x : Plane) : ‖x‖ ^ 2 = dot2 x x := by
  simpa [dot2, Fin.sum_univ_two, pow_two] using
    EuclideanSpace.real_norm_sq_eq x

private theorem dist_sq_eq_dot2 (x y : Plane) :
    dist x y ^ 2 = dot2 x x + dot2 y y - 2 * dot2 x y := by
  rw [dist_eq_norm, norm_sq_eq_dot2]
  simp [dot2]
  ring

private theorem dot_cross_identity (x y z : Plane) :
    dot2 x x * dot2 y z =
      dot2 x y * dot2 x z + cross2 x y * cross2 x z := by
  unfold dot2 cross2
  ring

private theorem two_of_three_products_nonneg (a b c : ℝ) :
    0 ≤ a * b ∨ 0 ≤ a * c ∨ 0 ≤ b * c := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · exact Or.inl (mul_nonneg ha hb)
    · by_cases hc : 0 ≤ c
      · exact Or.inr (Or.inl (mul_nonneg ha hc))
      · exact Or.inr (Or.inr (mul_nonneg_of_nonpos_of_nonpos
          (le_of_not_ge hb) (le_of_not_ge hc)))
  · by_cases hb : b ≤ 0
    · exact Or.inl (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) hb)
    · by_cases hc : c ≤ 0
      · exact Or.inr (Or.inl (mul_nonneg_of_nonpos_of_nonpos
          (le_of_not_ge ha) hc))
      · exact Or.inr (Or.inr (mul_nonneg (le_of_not_ge hb) (le_of_not_ge hc)))

private theorem dot2_neg_of_small_radius
    (x y : Plane) (hx : ‖x‖ < Real.sqrt 2)
    (hy : ‖y‖ < Real.sqrt 2) (hxy : 2 ≤ dist x y) :
    dot2 x y < 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnx : 0 ≤ ‖x‖ := norm_nonneg _
  have hny : 0 ≤ ‖y‖ := norm_nonneg _
  have hnxy : 0 ≤ dist x y := dist_nonneg
  have hxsq : ‖x‖ ^ 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hysq : ‖y‖ ^ 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hdsq : 4 ≤ dist x y ^ 2 := by nlinarith
  rw [dist_sq_eq_dot2, ← norm_sq_eq_dot2, ← norm_sq_eq_dot2] at hdsq
  linarith

/-- Separation two inside the open radius-`√2` disk forces an obtuse
angle at the origin. The statement includes the origin case vacuously. -/
theorem small_disk_pair_inner_neg (x y : Plane)
    (hx : ‖x‖ < Real.sqrt 2) (hy : ‖y‖ < Real.sqrt 2)
    (hxy : 2 ≤ dist x y) : ⟪x, y⟫_ℝ < 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hxsq : ‖x‖ ^ 2 < 2 := by
    nlinarith [norm_nonneg x, Real.sqrt_nonneg 2]
  have hysq : ‖y‖ ^ 2 < 2 := by
    nlinarith [norm_nonneg y, Real.sqrt_nonneg 2]
  have hdsq : 4 ≤ dist x y ^ 2 := by
    have hn : 0 ≤ dist x y := dist_nonneg
    nlinarith
  rw [dist_eq_norm, norm_sub_sq_real] at hdsq
  linarith

private theorem three_distance_sq_identity (x y z : Plane) :
    dist x y ^ 2 + dist y z ^ 2 + dist z x ^ 2 =
      3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) - ‖x + y + z‖ ^ 2 := by
  rw [dist_sq_eq_dot2, dist_sq_eq_dot2, dist_sq_eq_dot2,
    norm_sq_eq_dot2 x, norm_sq_eq_dot2 y, norm_sq_eq_dot2 z,
    norm_sq_eq_dot2 (x + y + z)]
  simp [dot2]
  ring

/-- A strict squared-radius bound for one of three separated points makes
the sharp three-point disk radius inequality strict. -/
theorem three_point_strict_radius_sq (x y z : Plane) (R : ℝ)
    (hxy : 2 ≤ dist x y) (hyz : 2 ≤ dist y z)
    (hzx : 2 ≤ dist z x)
    (hx : ‖x‖ ^ 2 < R ^ 2)
    (hy : ‖y‖ ^ 2 ≤ R ^ 2)
    (hz : ‖z‖ ^ 2 ≤ R ^ 2) :
    4 / 3 < R ^ 2 := by
  have hxy2 : 4 ≤ dist x y ^ 2 := by
    have hnonneg : 0 ≤ dist x y := dist_nonneg
    nlinarith
  have hyz2 : 4 ≤ dist y z ^ 2 := by
    have hnonneg : 0 ≤ dist y z := dist_nonneg
    nlinarith
  have hzx2 : 4 ≤ dist z x ^ 2 := by
    have hnonneg : 0 ≤ dist z x := dist_nonneg
    nlinarith
  have hsum := three_distance_sq_identity x y z
  have hnorm : 0 ≤ ‖x + y + z‖ ^ 2 := sq_nonneg _
  nlinarith

private theorem three_dot_contradiction (x y z : Plane)
    (hxy : dot2 x y < 0) (hxz : dot2 x z < 0)
    (hyz : dot2 y z < 0)
    (hcross : 0 ≤ cross2 x y * cross2 x z) : False := by
  have hprod : 0 < dot2 x y * dot2 x z :=
    mul_pos_of_neg_of_neg hxy hxz
  have hnorm : 0 ≤ dot2 x x := by
    rw [← norm_sq_eq_dot2]
    positivity
  have hlhs : dot2 x x * dot2 y z ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hnorm hyz.le
  have hrhs : 0 < dot2 x y * dot2 x z + cross2 x y * cross2 x z :=
    add_pos_of_pos_of_nonneg hprod hcross
  linarith [dot_cross_identity x y z]

/-- Four mutually separated planar points cannot all lie strictly inside
the radius-`sqrt 2` disk. This is the sharp square threshold. -/
theorem four_point_disk_obstruction (p : Fin 4 → Plane)
    (hsep : Separated p 2) :
    ∃ i : Fin 4, Real.sqrt 2 ≤ ‖p i‖ := by
  by_contra h
  push Not at h
  have h01 := dot2_neg_of_small_radius (p 0) (p 1)
    (h 0) (h 1) (hsep 0 1 (by decide))
  have h02 := dot2_neg_of_small_radius (p 0) (p 2)
    (h 0) (h 2) (hsep 0 2 (by decide))
  have h03 := dot2_neg_of_small_radius (p 0) (p 3)
    (h 0) (h 3) (hsep 0 3 (by decide))
  have h12 := dot2_neg_of_small_radius (p 1) (p 2)
    (h 1) (h 2) (hsep 1 2 (by decide))
  have h13 := dot2_neg_of_small_radius (p 1) (p 3)
    (h 1) (h 3) (hsep 1 3 (by decide))
  have h23 := dot2_neg_of_small_radius (p 2) (p 3)
    (h 2) (h 3) (hsep 2 3 (by decide))
  rcases two_of_three_products_nonneg
      (cross2 (p 0) (p 1)) (cross2 (p 0) (p 2))
      (cross2 (p 0) (p 3)) with h12cross | h13cross | h23cross
  · exact three_dot_contradiction (p 0) (p 1) (p 2)
      h01 h02 h12 h12cross
  · exact three_dot_contradiction (p 0) (p 1) (p 3)
      h01 h03 h13 h13cross
  · exact three_dot_contradiction (p 0) (p 2) (p 3)
      h02 h03 h23 h23cross

end CP15
