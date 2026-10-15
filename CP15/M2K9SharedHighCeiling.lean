import CP15.M2K9SharedAllLowBridge
import CP15.K9ScalarBounds
import CP15.ParametricOuterGap

namespace CP15

/-- Exact rational angle budget: two high touching inner centers with
radii at least `23094/10000` and `57/25` cannot fit in a nine-center
outer ring. The tiny margin is checked by rational polynomial bounds. -/
theorem k9_two_high_radius_57_div_25_budget_impossible
    (b s z δ₀ δ₁ : ℝ)
    (hb : 3 < b) (hbB : b ≤ (352136 / 100000 : ℝ))
    (hslo : (23094 / 10000 : ℝ) ≤ s) (hshi : s ≤ 12 / 5)
    (hzlo : (57 / 25 : ℝ) ≤ z) (hzhi : z ≤ 12 / 5)
    (hδ₀0 : 0 ≤ δ₀) (hδ₀pi : δ₀ ≤ Real.pi)
    (hδ₁0 : 0 ≤ δ₁) (hδ₁pi : δ₁ ≤ Real.pi)
    (hlaw₀ : 2 * s * b * Real.cos δ₀ = b ^ 2 + s ^ 2 - 4)
    (hlaw₁ : 2 * z * b * Real.cos δ₁ = b ^ 2 + z ^ 2 - 4)
    (hbudget : 2 * δ₀ + 2 * δ₁ +
      7 * (57588 / 100000 : ℝ) ≤ 2 * Real.pi) : False := by
  have hθ₀ : (56535 / 100000 : ℝ) < δ₀ := by
    apply contact_offset_gt_rational_angle b (352136 / 100000)
      (23094 / 10000) s δ₀ (56535 / 100000)
      hb hbB (by norm_num) (by norm_num) hslo hshi
      hδ₀0 hδ₀pi (by norm_num) (by norm_num)
    · norm_num [contactCos, sinCubicUpper]
    · exact hlaw₀
  have hθ₁ : (56070 / 100000 : ℝ) < δ₁ := by
    apply contact_offset_gt_rational_angle b (352136 / 100000)
      (57 / 25) z δ₁ (56070 / 100000)
      hb hbB (by norm_num) (by norm_num) hzlo hzhi
      hδ₁0 hδ₁pi (by norm_num) (by norm_num)
    · norm_num [contactCos, sinCubicUpper]
    · exact hlaw₁
  have hpi := Real.pi_lt_d6
  linarith

/-- Radius ceiling for the second high touching inner center in the
shared-blocker branch. Both outer contacts are actual contacts; their
charged gaps are distinct by the checked collision theorem. -/
theorem k9_second_high_radius_lt_57_div_25
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hbcut : 2 * Real.sqrt 3 < b)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK9 : (boundarySet p b).card = 9)
    (q z : Fin 15) (hqz : q ≠ z)
    (hq : ‖p q‖ < b ∧ TouchesOuter p b q)
    (hz : ‖p z‖ < b ∧ TouchesOuter p b z)
    (hqsq : (16 / 3 : ℝ) < ‖p q‖ ^ 2)
    (hzrad : 2 < ‖p z‖) :
    ‖p z‖ < 57 / 25 := by
  classical
  by_contra hnot
  have hzlo : (57 / 25 : ℝ) ≤ ‖p z‖ := le_of_not_gt hnot
  have hqlo : (23094 / 10000 : ℝ) ≤ ‖p q‖ := by
    have hn := norm_nonneg (p q)
    nlinarith
  let inner : Fin 2 → Fin 15 := ![q, z]
  let outer : Fin 2 → Fin 15 :=
    fun t => if t = 0 then Classical.choose hq.2 else Classical.choose hz.2
  have hinj : Function.Injective inner := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [inner]
  have hinner (t : Fin 2) : ‖p (inner t)‖ < b := by
    fin_cases t
    · simpa [inner] using hq.1
    · simpa [inner] using hz.1
  have hradius (t : Fin 2) : 2 ≤ ‖p (inner t)‖ := by
    fin_cases t
    · have hn := norm_nonneg (p q)
      have : 2 < ‖p q‖ := by nlinarith [hqsq]
      exact this.le
    · exact hzrad.le
  have houter (t : Fin 2) : ‖p (outer t)‖ = b := by
    fin_cases t
    · simpa [outer] using (Classical.choose_spec hq.2).2.1
    · simpa [outer] using (Classical.choose_spec hz.2).2.1
  have htouch (t : Fin 2) :
      dist (p (inner t)) (p (outer t)) = 2 := by
    fin_cases t
    · simpa [inner, outer] using (Classical.choose_spec hq.2).2.2
    · simpa [inner, outer] using (Classical.choose_spec hz.2).2.2
  obtain ⟨charge, offset, hcharge, hoffset, _, _⟩ :=
    exists_large_contact_exact_gap_budget p b hb hbB hsep hD
      (by omega) inner outer hinj hinner hradius houter htouch
  have hsize : (boundaryAngles p b).card = 9 := by
    rw [boundaryAngles_card p b hsep]
    exact hK9
  have hsize2 : 2 ≤ (boundaryAngles p b).card := by omega
  have himage : (Finset.univ.image charge).card = 2 := by
    simp [Finset.card_image_of_injective _ hcharge]
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hcompcard :
      (Finset.univ \ Finset.univ.image charge).card = 7 := by
    rw [Finset.card_sdiff_of_subset hsubset, himage]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hstrong : (∑ t : Fin 2, 2 * offset t) +
      (∑ _u ∈ Finset.univ \ Finset.univ.image charge,
        (57588 / 100000 : ℝ)) ≤ 2 * Real.pi := by
    exact injective_gap_budget Finset.univ charge
      (fun t => 2 * offset t)
      (nextBoundaryGap p b hsize2) (57588 / 100000) (2 * Real.pi)
      hcharge (by simp) (fun t => (hoffset t).2.1)
      (fun u _ => every_next_gap_ge_57588_div_100000 p b
        (by linarith) hbB hsep hsize2 u)
      (sum_next_boundary_gaps p b hsize2)
  have hbudget : 2 * offset 0 + 2 * offset 1 +
      7 * (57588 / 100000 : ℝ) ≤ 2 * Real.pi := by
    rw [Fin.sum_univ_two] at hstrong
    simp only [Finset.sum_const, nsmul_eq_mul, hcompcard] at hstrong
    linarith
  have hδpi (t : Fin 2) : offset t ≤ Real.pi := by
    have hgap := every_next_gap_lt_pi p b (by linarith) hbB
      hsep (by omega) (charge t)
    linarith [(hoffset t).2.1, (hoffset t).1]
  have hsupper : ‖p q‖ ≤ 12 / 5 :=
    ((hD q hq.1).trans
      (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)).le
  have hzupper : ‖p z‖ ≤ 12 / 5 :=
    ((hD z hz.1).trans
      (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)).le
  have hbq : b ≤ (352136 / 100000 : ℝ) :=
    (hbB.trans_lt Candidate.candidateB_lt_352136_div_100000).le
  have hb3 : 3 < b := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg 3
    nlinarith
  have hlaw₀ : 2 * ‖p q‖ * b * Real.cos (offset 0) =
      b ^ 2 + ‖p q‖ ^ 2 - 4 := by
    simpa [inner] using (hoffset 0).2.2
  have hlaw₁ : 2 * ‖p z‖ * b * Real.cos (offset 1) =
      b ^ 2 + ‖p z‖ ^ 2 - 4 := by
    simpa [inner] using (hoffset 1).2.2
  exact k9_two_high_radius_57_div_25_budget_impossible
    b ‖p q‖ ‖p z‖ (offset 0) (offset 1)
    hb3 hbq hqlo hsupper hzlo hzupper
    (by linarith [(hoffset 0).1]) (hδpi 0)
    (by linarith [(hoffset 1).1]) (hδpi 1)
    hlaw₀ hlaw₁ hbudget

/-- The current exact geometric residual of the shared branch. -/
theorem k9_shared_blocker_high_pair_residual
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hbcut : 2 * Real.sqrt 3 < b)
    (hK9 : (boundarySet p b).card = 9)
    (hm2 : (nonOuterIndices p b).card = 2)
    (target : Fin 2 → Fin 15) (htarget : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c))
    (blocker : Fin 15)
    (hblock : ‖p blocker‖ < b ∧
      2 < ‖p blocker‖ ∧ TouchesOuter p b blocker)
    (hqsq : (16 / 3 : ℝ) < ‖p blocker‖ ^ 2) :
    ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2 ∧
    ∃ z ∈ touchingInnerSet p b,
      z ≠ blocker ∧ 2 < ‖p z‖ ∧ ‖p z‖ < 57 / 25 := by
  have hcard := k9_shared_high_touching_inner_card_eq_two
    p b hb hbB hpack hD hFcap hbcut hK9 hm2 target htarget hno
    blocker hblock
  obtain ⟨z, hzT, hne, hzrad⟩ :=
    k9_shared_blocker_not_unique_high p b hb hbB hpack hD hFcap
      hbcut hK9 hm2 target htarget hno blocker hblock
  have hz : ‖p z‖ < b ∧ TouchesOuter p b z := by
    simpa [touchingInnerSet] using hzT
  exact ⟨hcard, z, hzT, hne, hzrad,
    k9_second_high_radius_lt_57_div_25 p b hb hbB hbcut
      hpack.2 hD hK9 blocker z hne.symm
      ⟨hblock.1, hblock.2.2⟩ hz hqsq hzrad⟩

end CP15
