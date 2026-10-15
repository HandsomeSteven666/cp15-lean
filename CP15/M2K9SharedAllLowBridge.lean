import CP15.M2K9AllLow
import CP15.M2K9Geometry
import CP15.M2K9HighCount

namespace CP15

theorem D_lt_shared_high_ceiling (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) :
    D b < 2385436 / 1000000 := by
  have hbq : b < (352136 / 100000 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_352136_div_100000
  have hrec : 4 / (352136 / 100000 : ℝ) < 4 / b := by
    apply (div_lt_div_iff₀ (by norm_num) (by linarith)).2
    nlinarith
  unfold D
  linarith

theorem touching_radius_gt_29_div_20
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 * Real.sqrt 3 < b) (i : Fin 15)
    (hi : TouchesOuter p b i) :
    (29 / 20 : ℝ) < ‖p i‖ := by
  obtain ⟨j, _, hj, hc⟩ := hi
  have ht := norm_add_le (p j - p i) (p i)
  rw [sub_add_cancel] at ht
  rw [dist_eq_norm] at hc
  have hswap : ‖p j - p i‖ = 2 := by
    simpa only [norm_sub_rev] using hc
  have hs : (69 / 40 : ℝ) < Real.sqrt 3 := by
    have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg 3
    nlinarith
  linarith

/-- In the shared-blocker branch at K=9, the blocker cannot be the
only touching inner center above radius two. This theorem uses actual
centers, not an assumed cyclic class word. -/
theorem k9_shared_blocker_not_unique_high
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
      2 < ‖p blocker‖ ∧ TouchesOuter p b blocker) :
    ∃ i ∈ touchingInnerSet p b,
      i ≠ blocker ∧ 2 < ‖p i‖ := by
  classical
  by_contra hnone
  have hother (i : Fin 15)
      (hi : i ∈ touchingInnerSet p b) (hne : i ≠ blocker) :
      ‖p i‖ ≤ 2 := by
    by_contra hrad
    exact hnone ⟨i, hi, hne, lt_of_not_ge hrad⟩
  let T := touchingInnerSet p b
  have hbmem : blocker ∈ T := by
    simpa [T, touchingInnerSet] using
      (⟨hblock.1, hblock.2.2⟩ :
        ‖p blocker‖ < b ∧ TouchesOuter p b blocker)
  have hTcard : T.card = 4 :=
    k9_m2_touching_inner_card_four p b hpack.1 hK9 hm2
  have hScard : (T.erase blocker).card = 3 := by
    rw [Finset.card_erase_of_mem hbmem, hTcard]
  have hthree : Fintype.card (Fin 3) ≤ (T.erase blocker).card := by
    simp [hScard]
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hthree
  have heT (c : Fin 3) : e c ∈ T ∧ e c ≠ blocker := by
    have hc : e c ∈ T.erase blocker := he ⟨c, rfl⟩
    exact ⟨(Finset.mem_erase.mp hc).2, (Finset.mem_erase.mp hc).1⟩
  have hedata (c : Fin 3) :
      ‖p (e c)‖ < b ∧ TouchesOuter p b (e c) := by
    simpa [T, touchingInnerSet] using (heT c).1
  have hFsmall := F_lt_1301_div_1000_of_le_candidateB b hb hbB
  have htargetHi (c : Fin 2) :
      ‖p (target c)‖ ≤ (1301 / 1000 : ℝ) :=
    (hFcap (target c) (hno c).1 (hno c).2).trans hFsmall.le
  have htargetSep := hpack.2 (target 0) (target 1)
    (htarget.ne (by decide))
  have htriangle := norm_sub_le (p (target 0)) (p (target 1))
  rw [dist_eq_norm] at htargetSep
  have htargetLo (c : Fin 2) :
      (699 / 1000 : ℝ) ≤ ‖p (target c)‖ := by
    fin_cases c
    · simpa using (show (699 / 1000 : ℝ) ≤ ‖p (target 0)‖ by
        linarith [htargetHi 1])
    · simpa using (show (699 / 1000 : ℝ) ≤ ‖p (target 1)‖ by
        linarith [htargetHi 0])
  have hblockHi : ‖p blocker‖ ≤ (2385436 / 1000000 : ℝ) :=
    ((hD blocker hblock.1).trans (D_lt_shared_high_ceiling b hb hbB)).le
  have heLo (c : Fin 3) :
      (29 / 20 : ℝ) ≤ ‖p (e c)‖ :=
    (touching_radius_gt_29_div_20 p b hbcut (e c) (hedata c).2).le
  have heHi (c : Fin 3) : ‖p (e c)‖ ≤ 2 :=
    hother (e c) (heT c).1 (heT c).2
  let idx (i : Fin 6) : Fin 15 :=
    if h : i.val < 2 then target ⟨i.val, h⟩
    else if h₂ : i.val = 2 then blocker
    else e ⟨i.val - 3, by omega⟩
  have hidx : Function.Injective idx := by
    intro i j hij
    by_cases hi : i.val < 2
    · by_cases hj : j.val < 2
      · have heq : (⟨i.val, hi⟩ : Fin 2) = ⟨j.val, hj⟩ := by
          apply htarget
          simpa only [idx, dif_pos hi, dif_pos hj] using hij
        exact Fin.ext (congrArg (fun t : Fin 2 => t.val) heq)
      · by_cases hj₂ : j.val = 2
        · have heq : target ⟨i.val, hi⟩ = blocker := by
            simpa only [idx, dif_pos hi, dif_neg hj, dif_pos hj₂] using hij
          exact False.elim ((hno ⟨i.val, hi⟩).2
            (heq ▸ hblock.2.2))
        · have heq : target ⟨i.val, hi⟩ =
              e ⟨j.val - 3, by omega⟩ := by
            simpa only [idx, dif_pos hi, dif_neg hj, dif_neg hj₂] using hij
          exact False.elim ((hno ⟨i.val, hi⟩).2
            (heq ▸ (hedata ⟨j.val - 3, by omega⟩).2))
    · by_cases hi₂ : i.val = 2
      · by_cases hj : j.val < 2
        · have heq : blocker = target ⟨j.val, hj⟩ := by
            simpa only [idx, dif_neg hi, dif_pos hi₂, dif_pos hj] using hij
          exact False.elim ((hno ⟨j.val, hj⟩).2
            (heq.symm ▸ hblock.2.2))
        · by_cases hj₂ : j.val = 2
          · exact Fin.ext (by omega)
          · have heq : blocker = e ⟨j.val - 3, by omega⟩ := by
              simpa only [idx, dif_neg hi, dif_pos hi₂, dif_neg hj, dif_neg hj₂] using hij
            exact False.elim ((heT ⟨j.val - 3, by omega⟩).2 heq.symm)
      · by_cases hj : j.val < 2
        · have heq : e ⟨i.val - 3, by omega⟩ = target ⟨j.val, hj⟩ := by
            simpa only [idx, dif_neg hi, dif_neg hi₂, dif_pos hj] using hij
          exact False.elim ((hno ⟨j.val, hj⟩).2
            (heq.symm ▸ (hedata ⟨i.val - 3, by omega⟩).2))
        · by_cases hj₂ : j.val = 2
          · have heq : e ⟨i.val - 3, by omega⟩ = blocker := by
              simpa only [idx, dif_neg hi, dif_neg hi₂, dif_neg hj, dif_pos hj₂] using hij
            exact False.elim ((heT ⟨i.val - 3, by omega⟩).2 heq)
          · have heq : (⟨i.val - 3, by omega⟩ : Fin 3) =
                ⟨j.val - 3, by omega⟩ := by
              apply e.injective
              simpa only [idx, dif_neg hi, dif_neg hi₂, dif_neg hj, dif_neg hj₂] using hij
            apply Fin.ext
            have hv := congrArg Fin.val heq
            dsimp at hv
            omega
  let q : Fin 6 → Plane := fun i => p (idx i)
  have hsepq : Separated q 2 := by
    intro i j hij
    exact hpack.2 (idx i) (idx j) (hidx.ne hij)
  have hrad (i : Fin 6) : if i.val < 2 then
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000
    else if i.val = 2 then
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000
    else (29 / 20 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2 := by
    by_cases hi : i.val < 2
    · simp only [hi, ↓reduceIte, q, idx, dif_pos hi]
      exact ⟨htargetLo ⟨i.val, hi⟩, htargetHi ⟨i.val, hi⟩⟩
    · by_cases hi₂ : i.val = 2
      · simp only [hi, hi₂, ↓reduceIte, q, idx, dif_neg hi, dif_pos hi₂]
        exact ⟨hblock.2.1.le, hblockHi⟩
      · simp only [hi, hi₂, ↓reduceIte, q, idx, dif_neg hi, dif_neg hi₂]
        exact ⟨heLo ⟨i.val - 3, by omega⟩,
          heHi ⟨i.val - 3, by omega⟩⟩
  exact shared_all_low_six_centers_impossible q hsepq hrad

/-- The actual shared-blocker branch has exactly two high-radius
touching inner centers: the blocker and one other center. -/
theorem k9_shared_high_touching_inner_card_eq_two
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
      2 < ‖p blocker‖ ∧ TouchesOuter p b blocker) :
    ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2 := by
  classical
  obtain ⟨i, hiT, hne, hirad⟩ :=
    k9_shared_blocker_not_unique_high p b hb hbB hpack hD hFcap
      hbcut hK9 hm2 target htarget hno blocker hblock
  let H := (touchingInnerSet p b).filter (fun j => 2 < ‖p j‖)
  have hbH : blocker ∈ H := by
    simp only [H, Finset.mem_filter]
    exact ⟨by simpa [touchingInnerSet] using
      (⟨hblock.1, hblock.2.2⟩ :
        ‖p blocker‖ < b ∧ TouchesOuter p b blocker), hblock.2.1⟩
  have hiH : i ∈ H := by
    simp only [H, Finset.mem_filter]
    exact ⟨hiT, hirad⟩
  have htwo : 2 ≤ H.card := by
    have hs : ({blocker, i} : Finset (Fin 15)) ⊆ H := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hbH
      · exact hiH
    have hc := Finset.card_le_card hs
    simpa [hne, hne.symm] using hc
  have hb3 : 3 < b := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg 3
    nlinarith
  have hupper := k9_high_touching_inner_count_le_two p b
    hb3 hbB hpack.2 hD hK9
  exact le_antisymm hupper htwo

end CP15
