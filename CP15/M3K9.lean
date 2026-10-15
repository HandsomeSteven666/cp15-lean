import CP15.K9ScalarCertificate
import CP15.M3DistinctBudget
import CP15.M3RadiusCutoff

open scoped InnerProductSpace

namespace CP15

/-- The normalized two-plus-one incidence branch at nine outer centers.
The two actual blockers are charged to distinct cyclic gaps, while the
third-target radius is supplied by the algebraic shared-blocker lemma. -/
theorem two_plus_one_blockers_impossible_at_K9
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hbcut : 2 * Real.sqrt 3 < b)
    (hK9 : (boundarySet p b).card = 9)
    (target blocker : Fin 3 → Fin 15)
    (htarget : Function.Injective target)
    (hdata : ∀ c, ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
      TouchesOuter p b (blocker c) ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (target c)‖ ^ 2 <
        ⟪p (blocker c), p (target c)⟫_ℝ)
    (c d e : Fin 3) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hsame : blocker c = blocker d)
    (hdiff : blocker c ≠ blocker e) : False := by
  classical
  have hroot : (3 / 2 : ℝ) < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hb3 : 3 < b := by linarith
  have hb12 : 12 < b ^ 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hBq : b ≤ (352136 / 100000 : ℝ) :=
    (hbB.trans_lt Candidate.candidateB_lt_352136_div_100000).le
  have hthird := selected_shared_pair_third_radius_and_blocker_sq p b
    hb hbB hpack.2 hD target blocker htarget
    (fun t => ⟨(hdata t).1, (hdata t).2.1,
      (hdata t).2.2.2.1, (hdata t).2.2.2.2⟩)
    c d e hcd hce hde hsame
  have hthirdblocksq := blocker_radius_sq (p (target e)) (p (blocker e))
    (hdata e).2.2.2.1 (hdata e).2.2.2.2
  have hsharedsq := selected_shared_blocker_sq_gt_sixteen_thirds p
    hpack.2 target blocker htarget
    (fun t => (hdata t).2.2.2.1)
    (fun t => (hdata t).2.2.2.2)
    c d hcd hsame
  have hslow : (11547 / 5000 : ℝ) ≤ ‖p (blocker c)‖ := by
    have hn := norm_nonneg (p (blocker c))
    nlinarith
  have hDbupper : D b < (238544 / 100000 : ℝ) := by
    have hBpos : (0 : ℝ) < 352136 / 100000 := by norm_num
    have hrec : 4 / (352136 / 100000 : ℝ) ≤ 4 / b := by
      apply (div_le_div_iff₀ hBpos (by linarith)).2
      nlinarith [hBq]
    have hcorner : (352136 / 100000 : ℝ) -
        4 / (352136 / 100000 : ℝ) < 238544 / 100000 := by norm_num
    unfold D
    linarith [hBq]
  have hshigh : ‖p (blocker c)‖ ≤ (14909 / 6250 : ℝ) := by
    have h := ((hD _ (hdata c).1).trans hDbupper).le
    norm_num at h ⊢
    exact h
  have hzupper : ‖p (blocker e)‖ ≤ 12 / 5 :=
    ((hD _ (hdata e).1).trans
      (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)).le
  let inner : Fin 2 → Fin 15 := fun t => if t = 0 then blocker c else blocker e
  have hinj : Function.Injective inner := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [inner]
  let outerWitness (t : Fin 2) : TouchesOuter p b (inner t) := by
    fin_cases t
    · simpa [inner] using (hdata c).2.2.1
    · simpa [inner] using (hdata e).2.2.1
  let outer : Fin 2 → Fin 15 := fun t => Classical.choose (outerWitness t)
  have houter (t : Fin 2) : ‖p (outer t)‖ = b ∧
      dist (p (inner t)) (p (outer t)) = 2 := by
    have ht := Classical.choose_spec (outerWitness t)
    exact ⟨ht.2.1, ht.2.2⟩
  have hinner (t : Fin 2) : ‖p (inner t)‖ < b := by
    fin_cases t
    · simpa [inner] using (hdata c).1
    · simpa [inner] using (hdata e).1
  have hradius (t : Fin 2) : 2 ≤ ‖p (inner t)‖ := by
    fin_cases t
    · simpa [inner] using (hdata c).2.1.le
    · simpa [inner] using (hdata e).2.1.le
  obtain ⟨charge, offset, hcharge, hoffset, _, _⟩ :=
    exists_large_contact_exact_gap_budget p b hb hbB hpack.2 hD
      (by omega) inner outer hinj hinner hradius
      (fun t => (houter t).1) (fun t => (houter t).2)
  have hsize : (boundaryAngles p b).card = 9 := by
    rw [boundaryAngles_card p b hpack.2]
    exact hK9
  have hsize2 : 2 ≤ (boundaryAngles p b).card := by omega
  have himage : (Finset.univ.image charge).card = 2 := by
    simp [Finset.card_image_of_injective _ hcharge]
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hcompcard : (Finset.univ \ Finset.univ.image charge).card = 7 := by
    rw [Finset.card_sdiff_of_subset hsubset, himage]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hstrong : (∑ t : Fin 2, 2 * offset t) +
      (∑ _u ∈ Finset.univ \ Finset.univ.image charge,
        (57588 / 100000 : ℝ)) ≤ 2 * Real.pi := by
    exact injective_gap_budget Finset.univ charge (fun t => 2 * offset t)
      (nextBoundaryGap p b hsize2) (57588 / 100000) (2 * Real.pi)
      hcharge (by simp) (fun t => (hoffset t).2.1)
      (fun u _ => every_next_gap_ge_57588_div_100000 p b
        (by linarith) hbB hpack.2 hsize2 u)
      (sum_next_boundary_gaps p b hsize2)
  have hbudget : 2 * offset 0 + 2 * offset 1 +
      7 * (57588 / 100000 : ℝ) ≤ 2 * Real.pi := by
    rw [Fin.sum_univ_two] at hstrong
    simp only [Finset.sum_const, nsmul_eq_mul, hcompcard] at hstrong
    linarith
  have hδpi (t : Fin 2) : offset t ≤ Real.pi := by
    have hgap := every_next_gap_lt_pi p b (by linarith) hbB
      hpack.2 (by omega) (charge t)
    have hle := (hoffset t).2.1
    have hpos := (hoffset t).1
    linarith
  have hlaw₀ : 2 * ‖p (blocker c)‖ * b * Real.cos (offset 0) =
      b ^ 2 + ‖p (blocker c)‖ ^ 2 - 4 := by
    simpa [inner] using (hoffset 0).2.2
  have hlaw₁ : 2 * ‖p (blocker e)‖ * b * Real.cos (offset 1) =
      b ^ 2 + ‖p (blocker e)‖ ^ 2 - 4 := by
    simpa [inner] using (hoffset 1).2.2
  exact k9_scalar_64_cell_certificate b ‖p (blocker c)‖
    ‖p (blocker e)‖ ‖p (target e)‖ (offset 0) (offset 1)
    hb3 hBq hb12 (hdata c).2.1 hslow hshigh
    (hdata e).2.1 hzupper hthird.1 (by linarith [hthirdblocksq])
    (by linarith [(hoffset 0).1]) (hδpi 0)
    (by linarith [(hoffset 1).1]) (hδpi 1)
    (by nlinarith [hlaw₀]) (by nlinarith [hlaw₁]) hbudget

/-- For the selected extremal representative, three non-outer centers
cannot coexist with exactly nine outer centers. The normalized two-plus-one
lemma covers all three labeled choices of the shared target pair. -/
theorem m3_impossible_at_K9
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hFcap : ∀ t, ‖p t‖ < b → ¬TouchesOuter p b t → ‖p t‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ t, ‖p t‖ < b → p t ≠ 0 →
      ∃ j, j ≠ t ∧ dist (p t) (p j) = 2 ∧
        ‖p t‖ ^ 2 < ⟪p j, p t⟫_ℝ)
    (hK9 : (boundarySet p b).card = 9)
    (hm3 : 3 ≤ (nonOuterIndices p b).card) : False := by
  classical
  have hbcut := m3_radius_cutoff p b hb hpack hD hblock hFcap
    hFsmall hm3
  obtain ⟨target, blocker, htarget, _, hdata, hpair, hnotall, _⟩ :=
    m3_selected_blockers_have_shared_pair p b hb hbB hpack hD hFcap
      hFsmall hblock (by omega) hm3
  rcases hpair with h01 | h02 | h12
  · have hdiff : blocker 0 ≠ blocker 2 := by
      intro h02
      exact hnotall ⟨h01, h01.symm.trans h02⟩
    exact two_plus_one_blockers_impossible_at_K9 p b hb hbB hpack hD
      hbcut hK9 target blocker htarget hdata 0 1 2
      (by decide) (by decide) (by decide) h01 hdiff
  · have hdiff : blocker 0 ≠ blocker 1 := by
      intro h01
      exact hnotall ⟨h01, h01.symm.trans h02⟩
    exact two_plus_one_blockers_impossible_at_K9 p b hb hbB hpack hD
      hbcut hK9 target blocker htarget hdata 0 2 1
      (by decide) (by decide) (by decide) h02 hdiff
  · have hdiff : blocker 1 ≠ blocker 0 := by
      intro h10
      exact hnotall ⟨h10.symm, h12⟩
    exact two_plus_one_blockers_impossible_at_K9 p b hb hbB hpack hD
      hbcut hK9 target blocker htarget hdata 1 2 0
      (by decide) (by decide) (by decide) h12 hdiff

end CP15
