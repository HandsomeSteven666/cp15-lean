import CP15.M3K8Seven

open scoped InnerProductSpace

namespace CP15

noncomputable def touchingInnerSet (p : Fin 15 → Plane) (b : ℝ) :
    Finset (Fin 15) := by
  classical
  exact Finset.univ.filter (fun i => ‖p i‖ < b ∧ TouchesOuter p b i)

/-- With at most eight boundary centers and at most three non-outer
centers, four other centers lie strictly inside and touch the boundary. -/
theorem four_touching_inner_available
    (p : Fin 15 → Plane) (b : ℝ) (hpack : InDisk b p)
    (hK : (boundarySet p b).card ≤ 8)
    (hm : (nonOuterIndices p b).card ≤ 3) :
    4 ≤ (touchingInnerSet p b).card := by
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
  change B.card ≤ 8 at hK
  change M.card ≤ 3 at hm
  change 4 ≤ T.card
  omega

theorem touching_inner_radius_gt_seven_fifths
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 * Real.sqrt 3 < b)
    (i : Fin 15) (hi : TouchesOuter p b i) :
    (7 / 5 : ℝ) < ‖p i‖ := by
  have hs : (17 / 10 : ℝ) < Real.sqrt 3 := by
    have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg 3
    nlinarith
  obtain ⟨j, _, hj, hc⟩ := hi
  have ht := norm_add_le (p j - p i) (p i)
  rw [sub_add_cancel] at ht
  rw [dist_eq_norm] at hc
  have hswap : ‖p j - p i‖ = 2 := by
    simpa only [norm_sub_rev] using hc
  linarith

theorem inner_radius_lt_14909_div_6250
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (i : Fin 15) (hi : ‖p i‖ < b) :
    ‖p i‖ < (14909 / 6250 : ℝ) := by
  have hbq : b < (352136 / 100000 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_352136_div_100000
  have hrec : 4 / (352136 / 100000 : ℝ) < 4 / b := by
    apply (div_lt_div_iff₀ (by norm_num) (by linarith)).2
    nlinarith
  have hcorner : (352136 / 100000 : ℝ) -
      4 / (352136 / 100000 : ℝ) < 14909 / 6250 := by norm_num
  have h := hD i hi
  unfold D at h
  linarith

/-- The at-most-eight-boundary branch of the three-nonouter exclusion.
The seven extracted centers are embedded into the original fifteen, so
all separation and contact properties are inherited without a graph
enumeration or an implicit convexity assumption. -/
theorem m3_impossible_at_K_le_8
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hK : (boundarySet p b).card ≤ 8)
    (hm3 : 3 ≤ (nonOuterIndices p b).card) : False := by
  classical
  have hmle := nonOuter_count_le_three p b hpack.2 hFcap hFsmall
  have hthree : Fintype.card (Fin 3) ≤
      (nonOuterIndices p b).card := by simpa using hm3
  obtain ⟨eL, heL⟩ := Function.Embedding.exists_of_card_le_finset hthree
  have hfour : Fintype.card (Fin 4) ≤
      (touchingInnerSet p b).card := by
    simpa using four_touching_inner_available p b hpack.1 hK hmle
  obtain ⟨eH, heH⟩ := Function.Embedding.exists_of_card_le_finset hfour
  have hL (a : Fin 3) :
      ‖p (eL a)‖ < b ∧ ¬TouchesOuter p b (eL a) := by
    have ha : eL a ∈ nonOuterIndices p b := heL ⟨a, rfl⟩
    simpa [nonOuterIndices] using ha
  have hH (a : Fin 4) :
      ‖p (eH a)‖ < b ∧ TouchesOuter p b (eH a) := by
    have ha : eH a ∈ touchingInnerSet p b := heH ⟨a, rfl⟩
    simpa [touchingInnerSet] using ha
  have hFq := F_lt_1301_div_1000_of_le_candidateB b hb hbB
  have hLhi (a : Fin 3) : ‖p (eL a)‖ ≤ (1301 / 1000 : ℝ) :=
    (hFcap (eL a) (hL a).1 (hL a).2).trans hFq.le
  have hLlo (a : Fin 3) : (4 / 5 : ℝ) ≤ ‖p (eL a)‖ := by
    fin_cases a
    · exact (three_separated_small_centers_radius_gt_four_fifths
        (p (eL 0)) (p (eL 1)) (p (eL 2))
        (hLhi 0) (hLhi 1) (hLhi 2)
        (hpack.2 _ _ (eL.injective.ne (by decide)))
        (hpack.2 _ _ (eL.injective.ne (by decide)))
        (hpack.2 _ _ (eL.injective.ne (by decide)))).le
    · exact (three_separated_small_centers_radius_gt_four_fifths
        (p (eL 1)) (p (eL 0)) (p (eL 2))
        (hLhi 1) (hLhi 0) (hLhi 2)
        (hpack.2 _ _ (eL.injective.ne (by decide)))
        (hpack.2 _ _ (eL.injective.ne (by decide)))
        (hpack.2 _ _ (eL.injective.ne (by decide)))).le
    · exact (three_separated_small_centers_radius_gt_four_fifths
        (p (eL 2)) (p (eL 0)) (p (eL 1))
        (hLhi 2) (hLhi 0) (hLhi 1)
        (hpack.2 _ _ (eL.injective.ne (by decide)))
        (hpack.2 _ _ (eL.injective.ne (by decide)))
        (hpack.2 _ _ (eL.injective.ne (by decide)))).le
  have hbcut := m3_radius_cutoff p b hb hpack hD hblock hFcap
    hFsmall hm3
  have hHlo (a : Fin 4) : (7 / 5 : ℝ) ≤ ‖p (eH a)‖ :=
    (touching_inner_radius_gt_seven_fifths p b hbcut (eH a) (hH a).2).le
  have hHhi (a : Fin 4) : ‖p (eH a)‖ ≤ (14909 / 6250 : ℝ) :=
    (inner_radius_lt_14909_div_6250 p b hb hbB hD (eH a) (hH a).1).le
  let idx (i : Fin 7) : Fin 15 :=
    if h : i.val < 3 then eL ⟨i.val, h⟩
    else eH ⟨i.val - 3, by omega⟩
  have hidx : Function.Injective idx := by
    intro i j hij
    by_cases hi : i.val < 3
    · by_cases hj : j.val < 3
      · have he : (⟨i.val, hi⟩ : Fin 3) = ⟨j.val, hj⟩ :=
          eL.injective (by simpa only [idx, dif_pos hi, dif_pos hj] using hij)
        exact Fin.ext (congrArg (fun k : Fin 3 => k.val) he)
      · have he : eL ⟨i.val, hi⟩ = eH ⟨j.val - 3, by omega⟩ := by
          simpa only [idx, dif_pos hi, dif_neg hj] using hij
        exact False.elim ((hL ⟨i.val, hi⟩).2 (he ▸ (hH ⟨j.val - 3, by omega⟩).2))
    · by_cases hj : j.val < 3
      · have he : eH ⟨i.val - 3, by omega⟩ = eL ⟨j.val, hj⟩ := by
          simpa only [idx, dif_neg hi, dif_pos hj] using hij
        exact False.elim ((hL ⟨j.val, hj⟩).2 (he.symm ▸ (hH ⟨i.val - 3, by omega⟩).2))
      · have he : (⟨i.val - 3, by omega⟩ : Fin 4) =
            ⟨j.val - 3, by omega⟩ :=
          eH.injective (by simpa only [idx, dif_neg hi, dif_neg hj] using hij)
        apply Fin.ext
        have hv := congrArg Fin.val he
        dsimp at hv
        omega
  let q : Fin 7 → Plane := fun i => p (idx i)
  have hsepq : Separated q 2 := by
    intro i j hij
    exact hpack.2 (idx i) (idx j) (hidx.ne hij)
  have hrad (i : Fin 7) : if i.val < 3 then
      (4 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 14909 / 6250 := by
    by_cases hi : i.val < 3
    · simp only [hi, ↓reduceIte, q, idx, dif_pos hi]
      exact ⟨hLlo ⟨i.val, hi⟩, hLhi ⟨i.val, hi⟩⟩
    · simp only [hi, ↓reduceIte, q, idx, dif_neg hi]
      exact ⟨hHlo ⟨i.val - 3, by omega⟩,
        hHhi ⟨i.val - 3, by omega⟩⟩
  exact seven_low_high_centers_impossible q hsepq hrad

end CP15
