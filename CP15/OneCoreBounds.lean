import CP15.FiveFrontier

namespace CP15

set_option maxHeartbeats 0

/-- Every center of the selected packing is nonzero. The origin case is
excluded through actual touching centers, not by a polar-coordinate
convention or a tacit domain restriction. -/
theorem SelectedPacking15.no_origin {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) (i : Fin 15) : p i ≠ 0 := by
  classical
  intro hzero
  have hb : 2 < b := centerFeasible_radius_gt_two h.optimal.1
  have hinner : ‖p i‖ < b := by rw [hzero, norm_zero]; linarith
  have hno : ¬TouchesOuter p b i := by
    rintro ⟨j, _, hj, hc⟩
    rw [hzero, dist_zero_left, hj] at hc
    linarith
  have hmem : i ∈ nonOuterIndices p b := by simp [nonOuterIndices, hinner, hno]
  have hmLo : 1 ≤ (nonOuterIndices p b).card := Finset.one_le_card.mpr ⟨i, hmem⟩
  have hm : (nonOuterIndices p b).card = 1 := by
    have hc := h.core_count_le_one
    omega
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  have hK7 : 7 ≤ (boundarySet p b).card := by have hc := h.touchingCount; omega
  have hrad (j : Fin 15) (hj : TouchesOuter p b j) : 2 ≤ ‖p j‖ := by
    have hji : j ≠ i := by intro heq; subst j; exact hno hj
    have hd := h.separated j i hji
    rwa [hzero, dist_zero_right] at hd
  by_cases hK8 : (boundarySet p b).card ≤ 8
  · obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
      (show Fintype.card (Fin 6) ≤ (touchingInnerSet p b).card by simp; omega)
    have hd (c : Fin 6) : ‖p (e c)‖ < b ∧ TouchesOuter p b (e c) := by
      have hm := he ⟨c, rfl⟩
      simpa [touchingInnerSet] using hm
    exact h.six_high_touching_impossible hK7 e e.injective
      (fun c => (hd c).1) (fun c => hrad (e c) (hd c).2) (fun c => (hd c).2)
  · have hK9 : 9 ≤ (boundarySet p b).card := by omega
    have ht3 : 3 ≤ (touchingInnerSet p b).card := by
      have hc := h.boundaryCount
      omega
    obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
      (show Fintype.card (Fin 3) ≤ (touchingInnerSet p b).card by simp; omega)
    have hd (c : Fin 3) : ‖p (e c)‖ < b ∧ TouchesOuter p b (e c) := by
      have hm := he ⟨c, rfl⟩
      simpa [touchingInnerSet] using hm
    choose outer hne houter hcontact using (fun c => (hd c).2)
    exact no_three_distinct_large_outer_contacts p b hb h.belowCandidate h.separated
      h.innerCap hK9 e outer e.injective (fun c => (hd c).1)
      (fun c => hrad (e c) (hd c).2) houter hcontact

theorem SelectedPacking15.touching_angle_gt_of_rational_corner
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (i : Fin 15) (hi : ‖p i‖ < b) (ht : TouchesOuter p b i)
    (l θ : ℝ) (hl : 0 < l) (hr : l ≤ ‖p i‖)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hcorner : contactCos (17607 / 5000) l < 1 - 2 * sinCubicUpper (θ / 2) ^ 2) :
    θ < contactAngle b ‖p i‖ := by
  have hb : 3 < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5, h.elementaryLower]
  have hbB : b ≤ (17607 / 5000 : ℝ) :=
    (h.belowCandidate.trans_lt Candidate.candidateB_lt_352136_div_100000).le.trans (by norm_num)
  obtain ⟨j, _, hj, hc⟩ := ht
  have hlaw := actual_contactAngle_cosine_law (p i) (p j) b (by linarith) (hl.trans_le hr) hj hc
  exact contact_offset_gt_rational_angle b (17607 / 5000) l ‖p i‖
    (contactAngle b ‖p i‖) θ hb hbB (by norm_num) hl hr
    ((h.innerCap i hi).trans (D_lt_twelve_fifths_of_le_candidateB b (by linarith) h.belowCandidate)).le
    (Real.arccos_nonneg _) (Real.arccos_le_pi _) hθ0 hθ1 hcorner hlaw

/-- The sole core center in K=10 lies strictly between the two radius
cutoffs. The active strict blocker and the four touching centers are
constructed from the same selected packing. -/
theorem SelectedPacking15.K10_core_radius_bounds
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (i : Fin 15) (hi : ‖p i‖ < b) (hno : ¬TouchesOuter p b i) :
    (1 / 4 : ℝ) < ‖p i‖ ∧ ‖p i‖ < 1 := by
  classical
  have hmem : i ∈ nonOuterIndices p b := by simp [nonOuterIndices, hi, hno]
  have hm : (nonOuterIndices p b).card = 1 := by
    have hm0 := Finset.one_le_card.mpr ⟨i, hmem⟩
    have hm1 := h.core_count_le_one
    omega
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  have upper : ‖p i‖ < 1 := by
    by_contra hn
    have hri : 1 ≤ ‖p i‖ := le_of_not_gt hn
    obtain ⟨j, hji, hc, hdot⟩ := h.strictBlocker i hi (h.no_origin i)
    have hjinner := contact_of_nonOuter_is_inner p b h.inDisk i j hno hji hc
    have hjsq : (5 : ℝ) < ‖p j‖ ^ 2 := by
      nlinarith [blocker_radius_sq (p i) (p j) hc hdot]
    have hjLo : (2236067 / 1000000 : ℝ) ≤ ‖p j‖ := by
      nlinarith [norm_nonneg (p j)]
    have hj2 : 2 ≤ ‖p j‖ := by linarith
    have hjTouch := h.inner_ge_two_touches_outer j hjinner hj2
    have hγ := h.touching_angle_gt_of_rational_corner j hjinner hjTouch
      (2236067 / 1000000) (553 / 1000) (by norm_num) hjLo (by norm_num) (by norm_num)
      (by norm_num [contactCos, sinCubicUpper])
    have hbudget := h.touching_cost_budget (by omega) (fun _ : Fin 1 => j)
      (fun a c _ => Subsingleton.elim a c) (fun _ => hjinner) (fun _ => hjTouch)
    simp only [Fin.sum_univ_one, hK, Nat.cast_ofNat] at hbudget
    have hm := le_max_right (0 : ℝ) (2 * contactAngle b ‖p j‖ - 57588 / 100000)
    nlinarith [Real.pi_lt_d6]
  have lower : (1 / 4 : ℝ) < ‖p i‖ := by
    by_contra hn
    have hri : ‖p i‖ ≤ 1 / 4 := le_of_not_gt hn
    obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
      (show Fintype.card (Fin 4) ≤ (touchingInnerSet p b).card by simp; omega)
    have hd (c : Fin 4) : ‖p (e c)‖ < b ∧ TouchesOuter p b (e c) := by
      have hm := he ⟨c, rfl⟩
      simpa [touchingInnerSet] using hm
    have hr (c : Fin 4) : (7 / 4 : ℝ) ≤ ‖p (e c)‖ := by
      have hne : e c ≠ i := by intro heq; exact hno (heq ▸ (hd c).2)
      have hdist := h.separated (e c) i hne
      have hn := norm_sub_le (p (e c)) (p i)
      rw [← dist_eq_norm] at hn
      linarith
    have hγ (c : Fin 4) := h.touching_angle_gt_of_rational_corner (e c)
      (hd c).1 (hd c).2 (7 / 4) (47 / 125) (by norm_num) (hr c)
      (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])
    have hbudget := h.touching_cost_budget (by omega) e e.injective
      (fun c => (hd c).1) (fun c => (hd c).2)
    have heach (c : Fin 4) : (2 * (47 / 125) - 57588 / 100000 : ℝ) ≤
        max 0 (2 * contactAngle b ‖p (e c)‖ - 57588 / 100000) :=
      (by linarith [hγ c] : _ ≤ _).trans (le_max_right _ _)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => heach c)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at hsum
    simp only [hK, Nat.cast_ofNat] at hbudget
    nlinarith [Real.pi_lt_d6]
  exact ⟨lower, upper⟩

end CP15
