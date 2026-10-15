import CP15.ActualOuterCost
import CP15.SevenTouchingAngles

namespace CP15

set_option maxHeartbeats 0

theorem actual_contactAngle_cosine_law (x z : Plane) (b : ℝ)
    (hb : 0 < b) (hx : 0 < ‖x‖) (hz : ‖z‖ = b)
    (hcontact : dist x z = 2) :
    2 * ‖x‖ * b * Real.cos (contactAngle b ‖x‖) = b ^ 2 + ‖x‖ ^ 2 - 4 := by
  have hf := contact_inner_formula x z b ‖x‖ rfl hz hcontact
  rw [polar_inner, hz] at hf
  have hcp : contactCos b ‖x‖ = Real.cos (polarArg x - polarArg z) := by
    unfold contactCos
    apply (div_eq_iff (by positivity : (2 * b * ‖x‖) ≠ 0)).2
    nlinarith
  have hc : Real.cos (contactAngle b ‖x‖) = contactCos b ‖x‖ := by
    unfold contactAngle
    apply Real.cos_arccos
    · rw [hcp]; exact Real.neg_one_le_cos _
    · rw [hcp]; exact Real.cos_le_one _
  rw [hc, hcp]
  nlinarith

theorem SelectedPacking15.high_contact_angle_gt_27_5_degrees
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (i : Fin 15) (hi : ‖p i‖ < b) (hr : 2 ≤ ‖p i‖)
    (ht : TouchesOuter p b i) : 11 * Real.pi / 72 < contactAngle b ‖p i‖ := by
  have hb : 2 < b := centerFeasible_radius_gt_two h.optimal.1
  obtain ⟨j, _, hj, hc⟩ := ht
  have hlaw := actual_contactAngle_cosine_law (p i) (p j) b
    (by linarith) (by linarith) hj hc
  have hcos := contact_offset_cos_le_b_div_four b ‖p i‖ (contactAngle b ‖p i‖)
    hb hr (h.innerCap i hi) hlaw
  have hcθ : (353 / 400 : ℝ) < Real.cos (11 * Real.pi / 72) := by
    have htθ := cos_degrees_lower_of_certificate (55 / 2) (353 / 400)
      (by norm_num) (by norm_num) (by norm_num)
    convert htθ using 1 <;> ring
  have hbq := h.belowCandidate.trans_lt Candidate.candidateB_lt_353_div_100
  by_contra hn
  have hle : contactAngle b ‖p i‖ ≤ 11 * Real.pi / 72 := le_of_not_gt hn
  have hcmono := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
    (show 11 * Real.pi / 72 ≤ Real.pi by nlinarith [Real.pi_pos]) hle
  change Real.cos (11 * Real.pi / 72) ≤ Real.cos (contactAngle b ‖p i‖) at hcmono
  linarith

/-- Six high touching centers cannot fit in any selected packing with
seven or more boundary centers, even when their selected gaps collide. -/
theorem SelectedPacking15.six_high_touching_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : 7 ≤ (boundarySet p b).card)
    (inner : Fin 6 → Fin 15) (hinj : Function.Injective inner)
    (hinner : ∀ i, ‖p (inner i)‖ < b)
    (hr : ∀ i, 2 ≤ ‖p (inner i)‖)
    (ht : ∀ i, TouchesOuter p b (inner i)) : False := by
  have hbudget := h.touching_cost_budget hK inner hinj hinner ht
  have heach (i : Fin 6) :
      2 * (11 * Real.pi / 72) - (57588 / 100000 : ℝ) ≤
        max 0 (2 * contactAngle b ‖p (inner i)‖ - 57588 / 100000) := by
    have hc := h.high_contact_angle_gt_27_5_degrees (inner i) (hinner i) (hr i) (ht i)
    exact (by linarith : 2 * (11 * Real.pi / 72) - (57588 / 100000 : ℝ) ≤
      2 * contactAngle b ‖p (inner i)‖ - 57588 / 100000).trans (le_max_right _ _)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hsum
  have hcast : (7 : ℝ) ≤ ((boundarySet p b).card : ℝ) := by exact_mod_cast hK
  nlinarith [Real.pi_lt_d6]

/-- The two seven-touching rows are excluded directly from the selected
packing. Both the seven-center angle count and the outer collision budget
are proved from actual point positions. -/
theorem SelectedPacking15.seven_touching_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : 7 ≤ (boundarySet p b).card)
    (ht7 : 7 ≤ (touchingInnerSet p b).card) : False := by
  classical
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 7) ≤ (touchingInnerSet p b).card by simp; omega)
  have hd (i : Fin 7) : ‖p (e i)‖ < b ∧ TouchesOuter p b (e i) := by
    have hm := he ⟨i, rfl⟩
    simpa [touchingInnerSet] using hm
  have hb : (16 / 5 : ℝ) < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5, h.elementaryLower]
  have hlo (i : Fin 7) : (6 / 5 : ℝ) ≤ ‖p (e i)‖ := by
    obtain ⟨j, _, hj, hc⟩ := (hd i).2
    have hr := norm_add_le (p j - p (e i)) (p (e i))
    have hn : ‖p j - p (e i)‖ = 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hc
    rw [sub_add_cancel, hj, hn] at hr
    linarith
  have hhi (i : Fin 7) : ‖p (e i)‖ ≤ 2385436 / 1000000 :=
    ((h.innerCap (e i) (hd i).1).trans
      (D_lt_shared_high_ceiling b (by linarith) h.belowCandidate)).le
  have hlow := seven_touching_at_most_one_low (fun i => p (e i))
    (fun i j hij => h.separated _ _ (e.injective.ne hij)) hlo hhi
  let low := Finset.univ.filter (fun i : Fin 7 => ‖p (e i)‖ ≤ 2)
  let high := Finset.univ \ low
  have hhigh : 6 ≤ high.card := by
    have hc : high.card = 7 - low.card := by
      simp [high, Finset.card_sdiff_of_subset (show low ⊆ Finset.univ by simp)]
    have hl : low.card ≤ 1 := hlow
    omega
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 6) ≤ high.card by simp; omega)
  have hrad (i : Fin 6) : 2 ≤ ‖p (e (f i))‖ := by
    have hm := hf ⟨i, rfl⟩
    have hn : f i ∉ low := (Finset.mem_sdiff.mp hm).2
    simp [low] at hn
    exact hn.le
  exact h.six_high_touching_impossible hK (fun i => e (f i))
    (e.injective.comp f.injective) (fun i => (hd (f i)).1) hrad
    (fun i => (hd (f i)).2)

theorem SelectedPacking15.K7m1_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 7) (hm : (nonOuterIndices p b).card = 1) : False := by
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  exact h.seven_touching_impossible (by omega) (by omega)

theorem SelectedPacking15.K8m0_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 8) (hm : (nonOuterIndices p b).card = 0) : False := by
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  exact h.seven_touching_impossible (by omega) (by omega)

end CP15
