import CP15.M2NoSharedStrictBlocker

namespace CP15

theorem SelectedPacking15.inner_ge_two_touches_outer
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (i : Fin 15) (hi : ‖p i‖ < b) (hr : 2 ≤ ‖p i‖) : TouchesOuter p b i := by
  by_contra hn
  have hcap := h.coreCap i hi hn
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  linarith [h.coreCapSmall]

/-- The exact two-high-contact budget with the stronger checked rational
outer-gap baseline. Both offsets belong to actual, distinct charged gaps. -/
theorem SelectedPacking15.two_high_strong_budget
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK9 : (boundarySet p b).card = 9)
    (q z : Fin 15) (hqz : q ≠ z)
    (hq : ‖p q‖ < b) (hz : ‖p z‖ < b)
    (hq2 : 2 ≤ ‖p q‖) (hz2 : 2 ≤ ‖p z‖) :
    ∃ δ : Fin 2 → ℝ,
      (∀ i, 0 ≤ δ i ∧ δ i ≤ Real.pi) ∧
      2 * δ 0 + 2 * δ 1 + 7 * (57588 / 100000 : ℝ) ≤ 2 * Real.pi ∧
      2 * ‖p q‖ * b * Real.cos (δ 0) = b ^ 2 + ‖p q‖ ^ 2 - 4 ∧
      2 * ‖p z‖ * b * Real.cos (δ 1) = b ^ 2 + ‖p z‖ ^ 2 - 4 ∧
      δ 0 = Real.arccos (contactCos b ‖p q‖) ∧
      δ 1 = Real.arccos (contactCos b ‖p z‖) := by
  classical
  have hb : 2 < b := centerFeasible_radius_gt_two h.optimal.1
  have hqT := h.inner_ge_two_touches_outer q hq hq2
  have hzT := h.inner_ge_two_touches_outer z hz hz2
  let inner : Fin 2 → Fin 15 := ![q, z]
  let outer : Fin 2 → Fin 15 :=
    fun i => if i = 0 then Classical.choose hqT else Classical.choose hzT
  have hinj : Function.Injective inner := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [inner]
  have hinner (i : Fin 2) : ‖p (inner i)‖ < b := by
    fin_cases i
    · exact hq
    · exact hz
  have hradius (i : Fin 2) : 2 ≤ ‖p (inner i)‖ := by
    fin_cases i
    · exact hq2
    · exact hz2
  have houter (i : Fin 2) : ‖p (outer i)‖ = b := by
    fin_cases i
    · simpa [outer] using (Classical.choose_spec hqT).2.1
    · simpa [outer] using (Classical.choose_spec hzT).2.1
  have htouch (i : Fin 2) : dist (p (inner i)) (p (outer i)) = 2 := by
    fin_cases i
    · simpa [inner, outer] using (Classical.choose_spec hqT).2.2
    · simpa [inner, outer] using (Classical.choose_spec hzT).2.2
  obtain ⟨charge, δ, hcharge, hdata, _, hexact⟩ :=
    exists_large_contact_exact_gap_budget p b hb h.belowCandidate h.separated h.innerCap
      (by omega) inner outer hinj hinner hradius houter htouch
  have hsize : (boundaryAngles p b).card = 9 := by
    rw [boundaryAngles_card p b h.separated]
    exact hK9
  have hsize2 : 2 ≤ (boundaryAngles p b).card := by omega
  have hcomp : (Finset.univ \ Finset.univ.image charge).card = 7 := by
    rw [Finset.card_sdiff_of_subset (by simp), Finset.card_image_of_injective _ hcharge]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hstrong : (∑ i : Fin 2, 2 * δ i) +
      (∑ _u ∈ Finset.univ \ Finset.univ.image charge, (57588 / 100000 : ℝ)) ≤
        2 * Real.pi := by
    exact injective_gap_budget Finset.univ charge (fun i => 2 * δ i)
      (nextBoundaryGap p b hsize2) (57588 / 100000) (2 * Real.pi)
      hcharge (by simp) (fun i => (hdata i).2.1)
      (fun u _ => every_next_gap_ge_57588_div_100000 p b (by linarith)
        h.belowCandidate h.separated hsize2 u)
      (sum_next_boundary_gaps p b hsize2)
  have hδbounds (i : Fin 2) : 0 ≤ δ i ∧ δ i ≤ Real.pi := by
    have hgap := every_next_gap_lt_pi p b (by linarith) h.belowCandidate
      h.separated (by omega) (charge i)
    constructor <;> linarith [(hdata i).1, (hdata i).2.1]
  refine ⟨δ, hδbounds, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fin.sum_univ_two] at hstrong
    simp only [Finset.sum_const, nsmul_eq_mul, hcomp] at hstrong
    linarith
  · simpa [inner] using (hdata 0).2.2
  · simpa [inner] using (hdata 1).2.2
  · simpa [inner, contactCos, mul_comm, mul_left_comm, mul_assoc] using hexact 0
  · simpa [inner, contactCos, mul_comm, mul_left_comm, mul_assoc] using hexact 1

theorem k9_two_high_radius_23_div_10_budget_impossible
    (b s z d e : ℝ)
    (hb : 3 < b) (hbB : b ≤ (352136 / 100000 : ℝ))
    (hslo : (23 / 10 : ℝ) ≤ s) (hshi : s ≤ 12 / 5)
    (hzlo : (23 / 10 : ℝ) ≤ z) (hzhi : z ≤ 12 / 5)
    (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi) (he0 : 0 ≤ e) (hepi : e ≤ Real.pi)
    (hdlaw : 2 * s * b * Real.cos d = b ^ 2 + s ^ 2 - 4)
    (helaw : 2 * z * b * Real.cos e = b ^ 2 + z ^ 2 - 4)
    (hbudget : 2 * d + 2 * e + 7 * (57588 / 100000 : ℝ) ≤ 2 * Real.pi) : False := by
  have hδ (r δ : ℝ) (hrlo : (23 / 10 : ℝ) ≤ r) (hrhi : r ≤ 12 / 5)
      (hδ0 : 0 ≤ δ) (hδpi : δ ≤ Real.pi)
      (hlaw : 2 * r * b * Real.cos δ = b ^ 2 + r ^ 2 - 4) :
      (1127 / 2000 : ℝ) < δ := by
    apply contact_offset_gt_rational_angle b (352136 / 100000) (23 / 10) r δ
      (1127 / 2000) hb hbB (by norm_num) (by norm_num) hrlo hrhi
      hδ0 hδpi (by norm_num) (by norm_num)
    · norm_num [contactCos, sinCubicUpper]
    · exact hlaw
  have hd := hδ s d hslo hshi hd0 hdpi hdlaw
  have he := hδ z e hzlo hzhi he0 hepi helaw
  linarith [Real.pi_lt_d6]

theorem SelectedPacking15.two_high_min_radius_lt_23_div_10
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK9 : (boundarySet p b).card = 9) (hb3 : 3 < b)
    (q z : Fin 15) (hqz : q ≠ z)
    (hq : ‖p q‖ < b) (hz : ‖p z‖ < b)
    (hq2 : 2 ≤ ‖p q‖) (hz2 : 2 ≤ ‖p z‖) :
    ‖p q‖ < 23 / 10 ∨ ‖p z‖ < 23 / 10 := by
  by_contra hn
  push_neg at hn
  obtain ⟨δ, hδ, hbudget, hlaw0, hlaw1, _, _⟩ :=
    h.two_high_strong_budget hK9 q z hqz hq hz hq2 hz2
  have hqhi := (h.innerCap q hq).trans
    (D_lt_twelve_fifths_of_le_candidateB b (by linarith) h.belowCandidate)
  have hzhi := (h.innerCap z hz).trans
    (D_lt_twelve_fifths_of_le_candidateB b (by linarith) h.belowCandidate)
  exact k9_two_high_radius_23_div_10_budget_impossible b ‖p q‖ ‖p z‖ (δ 0) (δ 1)
    hb3 (h.belowCandidate.trans_lt Candidate.candidateB_lt_352136_div_100000).le
    hn.1 hqhi.le hn.2 hzhi.le (hδ 0).1 (hδ 0).2 (hδ 1).1 (hδ 1).2
    hlaw0 hlaw1 hbudget

end CP15
