import CP15.M2EightOrder
import CP15.M2RadiusCutoff

open scoped InnerProductSpace

namespace CP15

theorem six_touching_inner_available
    (p : Fin 15 → Plane) (b : ℝ) (hpack : InDisk b p)
    (hK : (boundarySet p b).card ≤ 7)
    (hm : (nonOuterIndices p b).card ≤ 2) :
    6 ≤ (touchingInnerSet p b).card := by
  classical
  let B := boundarySet p b
  let M := nonOuterIndices p b
  let T := touchingInnerSet p b
  have hcover : Finset.univ = B ∪ M ∪ T := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_union, true_iff]
    by_cases heq : ‖p i‖ = b
    · left; left; simpa [B, boundarySet] using heq
    · have hlt : ‖p i‖ < b := lt_of_le_of_ne (hpack i) heq
      by_cases ht : TouchesOuter p b i
      · right; simpa [T, touchingInnerSet] using And.intro hlt ht
      · left; right; simpa [M, nonOuterIndices] using And.intro hlt ht
  have hc := Finset.card_union_le (B ∪ M) T
  have hbm := Finset.card_union_le B M
  rw [← hcover] at hc
  have h15 : (Finset.univ : Finset (Fin 15)).card = 15 := by decide
  change B.card ≤ 7 at hK
  change M.card ≤ 2 at hm
  change 6 ≤ T.card
  omega

theorem m2_radius_gt_seventeen_fifths
    (p : Fin 15 → Plane) (b : ℝ) (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ q, ‖p q‖ < b → ‖p q‖ < D b)
    (hblock : ∀ q, ‖p q‖ < b → p q ≠ 0 →
      ∃ j, j ≠ q ∧ dist (p q) (p j) = 2 ∧
        ‖p q‖ ^ 2 < ⟪p j, p q⟫_ℝ)
    (hFcap : ∀ q, ‖p q‖ < b → ¬TouchesOuter p b q → ‖p q‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hm2 : 2 ≤ (nonOuterIndices p b).card) :
    (17 / 5 : ℝ) < b := by
  have hs5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs21 : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hs5pos := Real.sqrt_nonneg 5
  have hs21pos := Real.sqrt_nonneg 21
  have h5 : (223 / 100 : ℝ) < Real.sqrt 5 := by nlinarith
  have h21 : (457 / 100 : ℝ) < Real.sqrt 21 := by nlinarith
  have hbcut := m2_radius_cutoff p b hb hpack hD hblock hFcap
    hFsmall hm2
  linarith

theorem touching_inner_radius_gt_seven_fifths_of_b
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : (17 / 5 : ℝ) < b)
    (i : Fin 15) (hi : TouchesOuter p b i) :
    (7 / 5 : ℝ) < ‖p i‖ := by
  obtain ⟨j, _, hj, hc⟩ := hi
  have ht := norm_add_le (p j - p i) (p i)
  rw [sub_add_cancel] at ht
  rw [dist_eq_norm] at hc
  have hswap : ‖p j - p i‖ = 2 := by
    simpa only [norm_sub_rev] using hc
  linarith

/-- All `m = 2` packings with at most seven boundary centers are
excluded by an eight-center angular budget. -/
theorem m2_impossible_at_K_le_7
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hK : (boundarySet p b).card ≤ 7)
    (hm2 : 2 ≤ (nonOuterIndices p b).card)
    (hmle : (nonOuterIndices p b).card ≤ 2) : False := by
  classical
  have htwo : Fintype.card (Fin 2) ≤
      (nonOuterIndices p b).card := by simpa using hm2
  obtain ⟨eL, heL⟩ := Function.Embedding.exists_of_card_le_finset htwo
  have hsix : Fintype.card (Fin 6) ≤
      (touchingInnerSet p b).card := by
    simpa using six_touching_inner_available p b hpack.1 hK hmle
  obtain ⟨eH, heH⟩ := Function.Embedding.exists_of_card_le_finset hsix
  have hL (a : Fin 2) :
      ‖p (eL a)‖ < b ∧ ¬TouchesOuter p b (eL a) := by
    have ha : eL a ∈ nonOuterIndices p b := heL ⟨a, rfl⟩
    simpa [nonOuterIndices] using ha
  have hH (a : Fin 6) :
      ‖p (eH a)‖ < b ∧ TouchesOuter p b (eH a) := by
    have ha : eH a ∈ touchingInnerSet p b := heH ⟨a, rfl⟩
    simpa [touchingInnerSet] using ha
  have hFq := F_lt_1301_div_1000_of_le_candidateB b hb hbB
  have hLhi (a : Fin 2) : ‖p (eL a)‖ ≤ (1301 / 1000 : ℝ) :=
    (hFcap (eL a) (hL a).1 (hL a).2).trans hFq.le
  have hdist := hpack.2 (eL 0) (eL 1) (eL.injective.ne (by decide))
  have htriangle := norm_sub_le (p (eL 0)) (p (eL 1))
  rw [dist_eq_norm] at hdist
  have hLlo0 : (699 / 1000 : ℝ) ≤ ‖p (eL 0)‖ := by
    linarith [hLhi 1]
  have hLlo1 : (699 / 1000 : ℝ) ≤ ‖p (eL 1)‖ := by
    linarith [hLhi 0]
  have hLlo (a : Fin 2) : (699 / 1000 : ℝ) ≤ ‖p (eL a)‖ := by
    fin_cases a
    · exact hLlo0
    · exact hLlo1
  have hbcut := m2_radius_gt_seventeen_fifths p b hb hpack hD hblock
    hFcap hFsmall hm2
  have hHlo (a : Fin 6) : (7 / 5 : ℝ) ≤ ‖p (eH a)‖ :=
    (touching_inner_radius_gt_seven_fifths_of_b p b hbcut
      (eH a) (hH a).2).le
  have hHhi (a : Fin 6) : ‖p (eH a)‖ ≤ (14909 / 6250 : ℝ) :=
    (inner_radius_lt_14909_div_6250 p b hb hbB hD
      (eH a) (hH a).1).le
  let idx (i : Fin 8) : Fin 15 :=
    if h : i.val < 2 then eL ⟨i.val, h⟩
    else eH ⟨i.val - 2, by omega⟩
  have hidx : Function.Injective idx := by
    intro i j hij
    by_cases hi : i.val < 2
    · by_cases hj : j.val < 2
      · have he : (⟨i.val, hi⟩ : Fin 2) = ⟨j.val, hj⟩ :=
          eL.injective (by simpa only [idx, dif_pos hi, dif_pos hj] using hij)
        exact Fin.ext (congrArg (fun k : Fin 2 => k.val) he)
      · have he : eL ⟨i.val, hi⟩ = eH ⟨j.val - 2, by omega⟩ := by
          simpa only [idx, dif_pos hi, dif_neg hj] using hij
        exact False.elim ((hL ⟨i.val, hi⟩).2
          (he ▸ (hH ⟨j.val - 2, by omega⟩).2))
    · by_cases hj : j.val < 2
      · have he : eH ⟨i.val - 2, by omega⟩ = eL ⟨j.val, hj⟩ := by
          simpa only [idx, dif_neg hi, dif_pos hj] using hij
        exact False.elim ((hL ⟨j.val, hj⟩).2
          (he.symm ▸ (hH ⟨i.val - 2, by omega⟩).2))
      · have he : (⟨i.val - 2, by omega⟩ : Fin 6) =
            ⟨j.val - 2, by omega⟩ :=
          eH.injective (by simpa only [idx, dif_neg hi, dif_neg hj] using hij)
        apply Fin.ext
        have hv := congrArg Fin.val he
        dsimp at hv
        omega
  let q : Fin 8 → Plane := fun i => p (idx i)
  have hsepq : Separated q 2 := by
    intro i j hij
    exact hpack.2 (idx i) (idx j) (hidx.ne hij)
  have hrad (i : Fin 8) : if i.val < 2 then
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 14909 / 6250 := by
    by_cases hi : i.val < 2
    · simp only [hi, ↓reduceIte, q, idx, dif_pos hi]
      exact ⟨hLlo ⟨i.val, hi⟩, hLhi ⟨i.val, hi⟩⟩
    · simp only [hi, ↓reduceIte, q, idx, dif_neg hi]
      exact ⟨hHlo ⟨i.val - 2, by omega⟩,
        hHhi ⟨i.val - 2, by omega⟩⟩
  exact eight_low_high_centers_impossible q hsepq hrad

end CP15
