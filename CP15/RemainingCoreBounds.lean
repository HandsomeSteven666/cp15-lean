import CP15.OneCoreBounds

namespace CP15

set_option maxHeartbeats 0

theorem SelectedPacking15.core_radius_lt_131_div_100
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (i : Fin 15) (hi : ‖p i‖ < b) (hno : ¬TouchesOuter p b i) :
    ‖p i‖ < (131 / 100 : ℝ) := by
  have hb : 2 < b := centerFeasible_radius_gt_two h.optimal.1
  exact (h.coreCap i hi hno).trans_lt
    ((F_lt_1301_div_1000_of_le_candidateB b hb h.belowCandidate).trans (by norm_num))

/-- A small core would force every distinct touching center to have a
large radius. The actual collision-safe cost then exceeds a full turn. -/
theorem SelectedPacking15.core_radius_lower_of_touching_count
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (i : Fin 15) (hno : ¬TouchesOuter p b i)
    (n : ℕ) (hn : n ≤ (touchingInnerSet p b).card)
    (hK : 7 ≤ (boundarySet p b).card) (cut θ : ℝ)
    (hcut : cut < 2) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hcorner : contactCos (17607 / 5000) (2 - cut) < 1 - 2 * sinCubicUpper (θ / 2) ^ 2)
    (hover : 2 * Real.pi < (boundarySet p b).card * (57588 / 100000 : ℝ) +
      n * (2 * θ - 57588 / 100000)) : cut < ‖p i‖ := by
  classical
  by_contra hc
  have hri : ‖p i‖ ≤ cut := le_of_not_gt hc
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin n) ≤ (touchingInnerSet p b).card by simpa using hn)
  have hd (c : Fin n) : ‖p (e c)‖ < b ∧ TouchesOuter p b (e c) := by
    have hx := he ⟨c, rfl⟩
    simpa [touchingInnerSet] using hx
  have hr (c : Fin n) : 2 - cut ≤ ‖p (e c)‖ := by
    have hne : e c ≠ i := by intro heq; exact hno (heq ▸ (hd c).2)
    have hsep := h.separated _ _ hne
    have hn := norm_sub_le (p (e c)) (p i)
    rw [← dist_eq_norm] at hn
    linarith
  have hγ (c : Fin n) := h.touching_angle_gt_of_rational_corner (e c)
    (hd c).1 (hd c).2 (2 - cut) θ (by linarith) (hr c) hθ0 hθ1 hcorner
  have hbudget := h.touching_cost_budget hK e e.injective
    (fun c => (hd c).1) (fun c => (hd c).2)
  have heach (c : Fin n) : 2 * θ - 57588 / 100000 ≤
      max 0 (2 * contactAngle b ‖p (e c)‖ - 57588 / 100000) := by
    have hm := le_max_right (0 : ℝ) (2 * contactAngle b ‖p (e c)‖ - 57588 / 100000)
    linarith [hγ c]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => heach c)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

theorem SelectedPacking15.K8_core_radius_bounds
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 8)
    (i : Fin 15) (hi : ‖p i‖ < b) (hno : ¬TouchesOuter p b i) :
    (1 / 8 : ℝ) < ‖p i‖ ∧ ‖p i‖ < 131 / 100 := by
  have hmem : i ∈ nonOuterIndices p b := by simp [nonOuterIndices, hi, hno]
  have hm0 := Finset.one_le_card.mpr ⟨i, hmem⟩
  have hm1 := h.core_count_le_one
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  refine ⟨h.core_radius_lower_of_touching_count i hno 6 (by omega) (by omega)
    (1 / 8) (11 / 25) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [contactCos, sinCubicUpper]) ?_, h.core_radius_lt_131_div_100 i hi hno⟩
  rw [hK]
  norm_num
  linarith [Real.pi_lt_d6]

theorem SelectedPacking15.K9_core_radius_bounds
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 9)
    (i : Fin 15) (hi : ‖p i‖ < b) (hno : ¬TouchesOuter p b i) :
    (1 / 5 : ℝ) < ‖p i‖ ∧ ‖p i‖ < 131 / 100 := by
  have hmem : i ∈ nonOuterIndices p b := by simp [nonOuterIndices, hi, hno]
  have hm0 := Finset.one_le_card.mpr ⟨i, hmem⟩
  have hm1 := h.core_count_le_one
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  refine ⟨h.core_radius_lower_of_touching_count i hno 5 (by omega) (by omega)
    (1 / 5) (2 / 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [contactCos, sinCubicUpper]) ?_, h.core_radius_lt_131_div_100 i hi hno⟩
  rw [hK]
  norm_num
  linarith [Real.pi_lt_d6]

end CP15
