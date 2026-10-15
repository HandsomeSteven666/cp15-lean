import CP15.RemainingCoreBounds
import CP15.RationalRadianAngle

namespace CP15

set_option maxHeartbeats 0

theorem SelectedPacking15.touching_radius_gt_123_div_100
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (i : Fin 15) (_hi : ‖p i‖ < b) (ht : TouchesOuter p b i) :
    (123 / 100 : ℝ) < ‖p i‖ := by
  have hb : (323 / 100 : ℝ) < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5, h.elementaryLower]
  obtain ⟨j, _, hj, hc⟩ := ht
  have hn := norm_add_le (p j - p i) (p i)
  have hdist : ‖p j - p i‖ = 2 := by simpa [dist_eq_norm, norm_sub_rev] using hc
  rw [sub_add_cancel, hj, hdist] at hn
  linarith

/-- A single large actual touching center already violates the ten-gap
budget. This is slightly stronger than the radius 9/4 prerequisite used
by the paper's remaining interval certificates. -/
theorem SelectedPacking15.K10_touching_radius_lt
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (i : Fin 15) (hi : ‖p i‖ < b) (ht : TouchesOuter p b i) :
    ‖p i‖ < (2236067 / 1000000 : ℝ) := by
  by_contra hn
  have hr : (2236067 / 1000000 : ℝ) ≤ ‖p i‖ := le_of_not_gt hn
  have hγ := h.touching_angle_gt_of_rational_corner i hi ht
    (2236067 / 1000000) (553 / 1000) (by norm_num) hr (by norm_num) (by norm_num)
    (by norm_num [contactCos, sinCubicUpper])
  have hbudget := h.touching_cost_budget (by omega) (fun _ : Fin 1 => i)
    (fun a c _ => Subsingleton.elim a c) (fun _ => hi) (fun _ => ht)
  simp only [Fin.sum_univ_one, hK, Nat.cast_ofNat] at hbudget
  have hm := le_max_right (0 : ℝ) (2 * contactAngle b ‖p i‖ - 57588 / 100000)
  nlinarith [Real.pi_lt_d6]

theorem SelectedPacking15.K10_touching_radius_lt_nine_fourths
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (i : Fin 15) (hi : ‖p i‖ < b) (ht : TouchesOuter p b i) :
    ‖p i‖ < (9 / 4 : ℝ) := (h.K10_touching_radius_lt hK i hi ht).trans (by norm_num)

/-- Nine other actual outer gaps consume their proved baseline. -/
theorem SelectedPacking15.K10_next_gap_lt_111_div_100
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (hs : 2 ≤ (boundaryAngles p b).card) (u : Fin (boundaryAngles p b).card) :
    nextBoundaryGap p b hs u < (111 / 100 : ℝ) := by
  classical
  have hb : 0 < b := by
    have hc := centerFeasible_radius_gt_two h.optimal.1
    linarith
  have hbase (v : Fin (boundaryAngles p b).card) :=
    every_next_gap_ge_57588_div_100000 p b hb h.belowCandidate h.separated hs v
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase u) (fun v _ => hbase v)
  have hturn := sum_next_boundary_gaps p b hs
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := nextBoundaryGap p b hs)
    (Finset.mem_univ u)
  have hcard : (boundaryAngles p b).card = 10 := by
    rw [boundaryAngles_card p b h.separated, hK]
  have hcount : (Finset.univ.erase u).card = 9 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
      Fintype.card_fin, hcard]
  simp only [Finset.sum_const, hcount, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  rw [hturn] at hsplit
  linarith [Real.pi_lt_d6]

/-- Two low centers cannot fit into the same short occupied outer gap:
the bound holds for the actual lifted angular difference. -/
theorem low_touching_pair_angle_gt_23_div_20 (x y : Plane) (g : ℝ)
    (hxlo : (123 / 100 : ℝ) ≤ ‖x‖) (hxhi : ‖x‖ ≤ 9 / 5)
    (hylo : (123 / 100 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 9 / 5)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (23 / 20 : ℝ) < g := by
  apply directed_pair_box_radian_gt x y g (23 / 20) (2 / 5)
    (123 / 100) (9 / 5) (123 / 100) (9 / 5)
    (by norm_num) (by norm_num) hxlo hxhi hylo hyhi hsep hcos hg
    (by norm_num) (by norm_num)
  · exact cos_radians_lower_of_certificate _ _ (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [pairExpr]

end CP15
