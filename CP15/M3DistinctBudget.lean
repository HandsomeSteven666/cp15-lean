import CP15.BlockerCapacity

open scoped InnerProductSpace

namespace CP15

/-- The candidate-scale radial cap sharpens the contact offset to `12/25`.
The lower Taylor bound `1 - δ²/2 ≤ cos δ` and `b < 353/100` suffice. -/
theorem capped_large_contact_offset_gt_twelve_twentyfifths
    (b s δ : ℝ) (hb : 2 < b) (hbB : b ≤ candidateB)
    (hs : 2 ≤ s) (hsD : s < D b) (hδ0 : 0 ≤ δ)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    (12 / 25 : ℝ) < δ := by
  have hcos := contact_offset_cos_le_b_div_four b s δ hb hs hsD hlaw
  have hbq : b < (353 / 100 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_353_div_100
  by_contra hnot
  have hδhi : δ ≤ (12 / 25 : ℝ) := le_of_not_gt hnot
  have hδsq : δ ^ 2 ≤ (12 / 25 : ℝ) ^ 2 := by nlinarith
  have hTaylor := Real.one_sub_sq_div_two_le_cos (x := δ)
  nlinarith

/-- Three distinct inner centers of radius at least two, each contacting
the outer ring, would overdraw the actual cyclic gaps when `K ≥ 9`.
The conclusion uses no selected-blocker assumption. -/
theorem no_three_distinct_large_outer_contacts
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (inner outer : Fin 3 → Fin 15)
    (hinj : Function.Injective inner)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (hradius : ∀ c, 2 ≤ ‖p (inner c)‖)
    (houter : ∀ c, ‖p (outer c)‖ = b)
    (htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2) : False := by
  classical
  obtain ⟨charge, offset, hcharge, hdata, hbudget, _⟩ :=
    exists_large_contact_exact_gap_budget p b hb hbB hsep hD hK
      inner outer hinj hinner hradius houter htouch
  have hδ (c : Fin 3) : (12 / 25 : ℝ) < offset c :=
    capped_large_contact_offset_gt_twelve_twentyfifths b
      ‖p (inner c)‖ (offset c) hb hbB (hradius c)
      (hD _ (hinner c)) (by linarith [(hdata c).1])
      (hdata c).2.2
  have hcharged : (72 / 25 : ℝ) < ∑ c : Fin 3, 2 * offset c := by
    rw [Fin.sum_univ_three]
    linarith [hδ 0, hδ 1, hδ 2]
  have hsize : 9 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    exact hK
  have himage : (Finset.univ.image charge).card = 3 := by
    simp [Finset.card_image_of_injective _ hcharge]
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hcompcard : 6 ≤ (Finset.univ \ Finset.univ.image charge).card := by
    rw [Finset.card_sdiff_of_subset hsubset, himage]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hother : (24 / 7 : ℝ) ≤
      ∑ _u ∈ Finset.univ \ Finset.univ.image charge, (4 / 7 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcast : (6 : ℝ) ≤
        ((Finset.univ \ Finset.univ.image charge).card : ℝ) := by
      exact_mod_cast hcompcard
    nlinarith
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d20]
  linarith

/-- Actual inner centers of radius at least two that touch the outer ring. -/
noncomputable def highRadiusTouchingInnerIndices
    (p : Fin 15 → Plane) (b : ℝ) : Finset (Fin 15) := by
  classical
  exact Finset.univ.filter (fun i =>
    ‖p i‖ < b ∧ 2 ≤ ‖p i‖ ∧ TouchesOuter p b i)

/-- At least nine boundary centers leave room for at most two distinct
high-radius touching inner centers. -/
theorem highRadiusTouchingInnerIndices_card_le_two
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card) :
    (highRadiusTouchingInnerIndices p b).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : Fintype.card (Fin 3) ≤
      (highRadiusTouchingInnerIndices p b).card := by
    simpa using (show 3 ≤ (highRadiusTouchingInnerIndices p b).card by omega)
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hthree
  have hmem (c : Fin 3) : ‖p (e c)‖ < b ∧
      2 ≤ ‖p (e c)‖ ∧ TouchesOuter p b (e c) := by
    have hc : e c ∈ highRadiusTouchingInnerIndices p b := he ⟨c, rfl⟩
    simpa [highRadiusTouchingInnerIndices] using hc
  let outerWitness (c : Fin 3) := (hmem c).2.2
  let outer : Fin 3 → Fin 15 := fun c => Classical.choose (outerWitness c)
  have houter (c : Fin 3) : ‖p (outer c)‖ = b ∧
      dist (p (e c)) (p (outer c)) = 2 := by
    have hc := Classical.choose_spec (outerWitness c)
    exact ⟨hc.2.1, hc.2.2⟩
  exact no_three_distinct_large_outer_contacts p b hb hbB hsep hD
    hK e outer e.injective (fun c => (hmem c).1)
    (fun c => (hmem c).2.1) (fun c => (houter c).1)
    (fun c => (houter c).2)

/-- The selected blockers for three distinct non-outer centers have exactly
the two-plus-one incidence type: a pair shares one blocker, while the third
uses a different blocker. The all-shared pattern is excluded by capacity;
the all-distinct pattern is excluded by the strict outer-gap budget. -/
theorem three_nonOuter_selected_blockers_have_shared_pair
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hFcap : ∀ t, ‖p t‖ < b → ¬TouchesOuter p b t → ‖p t‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ t, ‖p t‖ < b → p t ≠ 0 →
      ∃ j, j ≠ t ∧ dist (p t) (p j) = 2 ∧
        ‖p t‖ ^ 2 < ⟪p j, p t⟫_ℝ)
    (hK : 9 ≤ (boundarySet p b).card)
    (target : Fin 3 → Fin 15) (hinj : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c)) :
    ∃ blocker : Fin 3 → Fin 15,
      (∀ c, ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
        TouchesOuter p b (blocker c) ∧
        dist (p (target c)) (p (blocker c)) = 2 ∧
        ‖p (target c)‖ ^ 2 <
          ⟪p (blocker c), p (target c)⟫_ℝ) ∧
      (blocker 0 = blocker 1 ∨ blocker 0 = blocker 2 ∨
        blocker 1 = blocker 2) ∧
      ¬(blocker 0 = blocker 1 ∧ blocker 1 = blocker 2) := by
  classical
  obtain ⟨blocker, hdata, hnotall, _⟩ :=
    three_nonOuter_blockers_not_all_shared p b hb hbB hpack hD
      hFcap hFsmall hblock hK target hinj hno
  have hnotinj : ¬Function.Injective blocker := by
    intro hblockinj
    let outerWitness (c : Fin 3) := (hdata c).2.2.1
    let outer : Fin 3 → Fin 15 := fun c => Classical.choose (outerWitness c)
    have houter (c : Fin 3) : ‖p (outer c)‖ = b ∧
        dist (p (blocker c)) (p (outer c)) = 2 := by
      have h := Classical.choose_spec (outerWitness c)
      exact ⟨h.2.1, h.2.2⟩
    exact no_three_distinct_large_outer_contacts p b hb hbB hpack.2 hD
      hK blocker outer hblockinj
      (fun c => (hdata c).1)
      (fun c => (hdata c).2.1.le)
      (fun c => (houter c).1)
      (fun c => (houter c).2)
  have hpair : blocker 0 = blocker 1 ∨ blocker 0 = blocker 2 ∨
      blocker 1 = blocker 2 := by
    by_cases h₀₁ : blocker 0 = blocker 1
    · exact Or.inl h₀₁
    · by_cases h₀₂ : blocker 0 = blocker 2
      · exact Or.inr (Or.inl h₀₂)
      · by_cases h₁₂ : blocker 1 = blocker 2
        · exact Or.inr (Or.inr h₁₂)
        · exfalso
          apply hnotinj
          intro a c h
          fin_cases a <;> fin_cases c <;> simp_all
  exact ⟨blocker, hdata, hpair, hnotall⟩

/-- Any shared selected blocker in a separated family of strict contacts
has squared radius above `16/3`. This applies independently of ring gaps. -/
theorem selected_shared_blocker_sq_gt_sixteen_thirds
    (p : Fin 15 → Plane) (hsep : Separated p 2)
    {ι : Type*} (target blocker : ι → Fin 15)
    (hinj : Function.Injective target)
    (hcontact : ∀ c, dist (p (target c)) (p (blocker c)) = 2)
    (hstrict : ∀ c, ‖p (target c)‖ ^ 2 <
      ⟪p (blocker c), p (target c)⟫_ℝ)
    (c d : ι) (hcd : c ≠ d) (hsame : blocker c = blocker d) :
    (16 / 3 : ℝ) < ‖p (blocker c)‖ ^ 2 := by
  have ht : target c ≠ target d := fun h => hcd (hinj h)
  apply two_strict_targets_force_blocker_sq_gt_sixteen_thirds
    (p (target c)) (p (target d)) (p (blocker c))
    (hcontact c)
    (by simpa [← hsame] using hcontact d)
    (hstrict c)
    (by simpa [← hsame] using hstrict d)
    (hsep _ _ ht)

/-- Cardinal form of the incidence reduction: if at least three centers
do not touch the outer ring, three of them admit selected strict blockers
with precisely the two-plus-one equality pattern. -/
theorem m3_selected_blockers_have_shared_pair
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hFcap : ∀ t, ‖p t‖ < b → ¬TouchesOuter p b t → ‖p t‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ t, ‖p t‖ < b → p t ≠ 0 →
      ∃ j, j ≠ t ∧ dist (p t) (p j) = 2 ∧
        ‖p t‖ ^ 2 < ⟪p j, p t⟫_ℝ)
    (hK : 9 ≤ (boundarySet p b).card)
    (hm3 : 3 ≤ (nonOuterIndices p b).card) :
    ∃ target blocker : Fin 3 → Fin 15,
      Function.Injective target ∧
      (∀ c, ‖p (target c)‖ < b ∧
        ¬TouchesOuter p b (target c)) ∧
      (∀ c, ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
        TouchesOuter p b (blocker c) ∧
        dist (p (target c)) (p (blocker c)) = 2 ∧
        ‖p (target c)‖ ^ 2 <
          ⟪p (blocker c), p (target c)⟫_ℝ) ∧
      (blocker 0 = blocker 1 ∨ blocker 0 = blocker 2 ∨
        blocker 1 = blocker 2) ∧
      ¬(blocker 0 = blocker 1 ∧ blocker 1 = blocker 2) ∧
      (∀ c d : Fin 3, c ≠ d → blocker c = blocker d →
        (16 / 3 : ℝ) < ‖p (blocker c)‖ ^ 2) := by
  classical
  have hthree : Fintype.card (Fin 3) ≤ (nonOuterIndices p b).card := by
    simpa using hm3
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hthree
  have hno (c : Fin 3) :
      ‖p (e c)‖ < b ∧ ¬TouchesOuter p b (e c) := by
    have hc : e c ∈ nonOuterIndices p b := he ⟨c, rfl⟩
    simpa [nonOuterIndices] using hc
  obtain ⟨blocker, hdata, hpair, hnotall⟩ :=
    three_nonOuter_selected_blockers_have_shared_pair p b hb hbB hpack
      hD hFcap hFsmall hblock hK e e.injective hno
  have hshared (c d : Fin 3) (hcd : c ≠ d)
      (hsame : blocker c = blocker d) :
      (16 / 3 : ℝ) < ‖p (blocker c)‖ ^ 2 := by
    exact selected_shared_blocker_sq_gt_sixteen_thirds p hpack.2
      e blocker e.injective
      (fun t => (hdata t).2.2.2.1)
      (fun t => (hdata t).2.2.2.2)
      c d hcd hsame
  exact ⟨e, blocker, e.injective, hno, hdata, hpair, hnotall, hshared⟩

end CP15
