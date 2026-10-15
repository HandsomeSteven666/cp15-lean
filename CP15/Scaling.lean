import CP15.Definitions

namespace CP15

def scale {n : ℕ} (t : ℝ) (p : Fin n → Plane) : Fin n → Plane :=
  fun i => t • p i

theorem norm_scale {n : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (p : Fin n → Plane) (i : Fin n) :
    ‖scale t p i‖ = t * ‖p i‖ := by
  simp [scale, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

theorem dist_scale {n : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (p : Fin n → Plane) (i j : Fin n) :
    dist (scale t p i) (scale t p j) = t * dist (p i) (p j) := by
  simp [scale, dist_eq_norm, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht]

theorem scale_center_to_point {n : ℕ} {b : ℝ}
    (hb : 0 < b) (h : CenterFeasible n b) :
    PointFeasible n (2 / b) := by
  rcases h with ⟨p, hp, hs⟩
  refine ⟨scale (1 / b) p, ?_, ?_⟩
  · intro i
    rw [norm_scale (1 / b) (by positivity)]
    have hi := hp i
    apply (mul_le_mul_of_nonneg_left hi (by positivity)).trans
    field_simp
    norm_num
  · intro i j hij
    rw [dist_scale (1 / b) (by positivity)]
    have hi := hs i j hij
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 / b by positivity)
    convert hh using 1
    field_simp

theorem scale_point_to_center {n : ℕ} {d : ℝ}
    (hd : 0 < d) (h : PointFeasible n d) :
    CenterFeasible n (2 / d) := by
  rcases h with ⟨p, hp, hs⟩
  refine ⟨scale (2 / d) p, ?_, ?_⟩
  · intro i
    rw [norm_scale (2 / d) (by positivity)]
    have hi := hp i
    simpa using mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 / d by positivity)
  · intro i j hij
    rw [dist_scale (2 / d) (by positivity)]
    have hi := hs i j hij
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 / d by positivity)
    convert hh using 1
    field_simp

theorem feasible_center_radius_pos {n : ℕ} {c : ℝ}
    (hpair : ∃ i j : Fin n, i ≠ j)
    (h : CenterFeasible n c) : 0 < c := by
  rcases hpair with ⟨i, j, hij⟩
  rcases h with ⟨p, hp, hs⟩
  have hpi : ‖p i‖ ≤ c := hp i
  have hpj : ‖p j‖ ≤ c := hp j
  by_contra hc
  have hc0 : c ≤ 0 := le_of_not_gt hc
  have hi : p i = 0 := norm_eq_zero.mp (le_antisymm (le_trans hpi hc0) (norm_nonneg _))
  have hj : p j = 0 := norm_eq_zero.mp (le_antisymm (le_trans hpj hc0) (norm_nonneg _))
  have hsep := hs i j hij
  simp [hi, hj] at hsep
  norm_num at hsep

theorem center_optimal_to_point_optimal {n : ℕ} {b : ℝ}
    (hb : 0 < b) (h : CenterOptimal n b) :
    PointOptimal n (2 / b) := by
  refine ⟨scale_center_to_point hb h.1, ?_⟩
  intro e he
  by_cases he0 : 0 < e
  · have hcenter := scale_point_to_center he0 he
    have hbound := h.2 (2 / e) hcenter
    apply (le_div_iff₀ hb).2
    have hbe : b * e ≤ 2 := (le_div_iff₀ he0).1 hbound
    nlinarith
  · have hnonpos : e ≤ 0 := le_of_not_gt he0
    exact hnonpos.trans (by positivity)

theorem point_optimal_to_center_optimal {n : ℕ} {d : ℝ}
    (hpair : ∃ i j : Fin n, i ≠ j)
    (hd : 0 < d) (h : PointOptimal n d) :
    CenterOptimal n (2 / d) := by
  refine ⟨scale_point_to_center hd h.1, ?_⟩
  intro c hc
  have hc0 : 0 < c := feasible_center_radius_pos hpair hc
  have hpoint := scale_center_to_point hc0 hc
  have hbound := h.2 (2 / c) hpoint
  have hdc : 2 ≤ d * c := (div_le_iff₀ hc0).1 hbound
  apply (div_le_iff₀ hd).2
  nlinarith

end CP15
