import CP15.SelectedFrontier
import CP15.LiftedContactClassification

open scoped InnerProductSpace

namespace CP15

private theorem cyclic_neighbor_pullback (f : Fin 6 → Fin 6)
    (hinj : Function.Injective f)
    (hcycle : (∀ i, f (i + 1) = f i + 1) ∨
      (∀ i, f (i + 1) + 1 = f i))
    (a b : Fin 6) (h : cyclicNeighbor (f a) (f b)) :
    cyclicNeighbor a b := by
  rcases hcycle with hf | hr
  · rcases h with h | h
    · left
      apply hinj
      rw [hf]
      exact h
    · right
      apply hinj
      rw [hf]
      exact h
  · rcases h with h | h
    · right
      apply hinj
      have hadd : Function.Injective (fun x : Fin 6 => x + 1) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> norm_num at *
      apply hadd
      change f a + 1 = f (b + 1) + 1
      rw [hr b]
      exact h.symm
    · left
      apply hinj
      have hadd : Function.Injective (fun x : Fin 6 => x + 1) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> norm_num at *
      apply hadd
      change f b + 1 = f (a + 1) + 1
      rw [hr a]
      exact h.symm

/-- The final two contact alternatives are now derived from the original
selected fifteen-center packing. The witness covers every inner index,
retains the selected strict A-H contacts, and records reversed orientation.
No principal-angle sorting premise is assumed after a cyclic reindexing. -/
theorem SelectedPacking15.actual_distinct_contact_split
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hm2 : (nonOuterIndices p b).card = 2) :
    ∃ ix : Fin 6 → Fin 15, ∃ φ : Fin 6 → ℝ, ∃ ε : ℝ,
      Function.Injective ix ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ i, ‖p (ix i)‖ < b) ∧
      (∀ j, ‖p j‖ < b → ∃ i, ix i = j) ∧
      LiftedSixFrame (fun i => p (ix i)) φ ε ∧
      Separated (fun i => p (ix i)) 2 ∧
      (∀ i, wordAHAHLL i = .A →
        (699 / 1000 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 1301 / 1000) ∧
      (∀ i, wordAHAHLL i = .H →
        (2 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2385436 / 1000000) ∧
      (∀ i, wordAHAHLL i = .L →
        (3 / 2 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2) ∧
      (dist (p (ix 0)) (p (ix 1)) = 2 ∧
        ‖p (ix 0)‖ ^ 2 < ⟪p (ix 1), p (ix 0)⟫_ℝ) ∧
      (dist (p (ix 2)) (p (ix 3)) = 2 ∧
        ‖p (ix 2)‖ ^ 2 < ⟪p (ix 3), p (ix 2)⟫_ℝ) ∧
      dist (p (ix 0)) (p (ix 5)) = 2 ∧
      (dist (p (ix 2)) (p (ix 0)) = 2 ∨
        dist (p (ix 2)) (p (ix 1)) = 2) := by
  classical
  obtain ⟨hK9, hbhalf, target, blocker, outer, htarget, hno, hdata, hne⟩ :=
    h.two_core_distinct hm2
  have hb : 2 < b := by linarith
  have hp : InDisk b p ∧ Separated p 2 := ⟨h.inDisk, h.separated⟩
  obtain ⟨q, ψ, w, hsep, hmono, harg, hfirst, hlast,
    _, _, _, hA, hH, hL, hselected, horbit,
    idx, hidx, hindex, hinner, hcover⟩ :=
    distinct_k9_actual_AHAHLL_word p b hb h.belowCandidate hp h.innerCap
      h.coreCap h.coreCapSmall h.strictBlocker hK9 hm2
      target blocker outer htarget hno hdata hne
  obtain ⟨f, φ, ε, hf, heps, hword, hframe, hcycle⟩ :=
    dihedral_word_actual_lift q ψ w
      (literal_six_frame q ψ hmono harg hfirst hlast) horbit
  let ix : Fin 6 → Fin 15 := fun i => idx (f i)
  let qc : Fin 6 → Plane := fun i => p (ix i)
  have hqc (i : Fin 6) : qc i = q (f i) := (hindex (f i)).symm
  have hframec : LiftedSixFrame qc φ ε := by simpa only [← hqc] using hframe
  have hAc (i : Fin 6) (hi : wordAHAHLL i = .A) :
      (699 / 1000 : ℝ) ≤ ‖qc i‖ ∧ ‖qc i‖ ≤ 1301 / 1000 := by
    rw [hqc]
    exact hA (f i) ((hword i).trans hi)
  have hHc (i : Fin 6) (hi : wordAHAHLL i = .H) :
      (2 : ℝ) ≤ ‖qc i‖ ∧ ‖qc i‖ ≤ 2385436 / 1000000 := by
    rw [hqc]
    exact hH (f i) ((hword i).trans hi)
  have hLc (i : Fin 6) (hi : wordAHAHLL i = .L) :
      (3 / 2 : ℝ) ≤ ‖qc i‖ ∧ ‖qc i‖ ≤ 2 := by
    have hl := hL (f i) ((hword i).trans hi)
    have ht : TouchesOuter p b (ix i) := by
      by_contra hn
      have hcap := h.coreCap (ix i) (hinner (f i)) hn
      have hF := F_lt_1301_div_1000_of_le_candidateB b hb h.belowCandidate
      rw [← hindex (f i)] at hcap
      linarith [hl.1]
    exact ⟨(touching_radius_ge_three_halves p b (ix i) hbhalf ht).le,
      by simpa [hqc] using hl.2⟩
  have hix : Function.Injective ix := hidx.comp hf.1
  have hinnerc (i : Fin 6) : ‖p (ix i)‖ < b := hinner (f i)
  have hcoverc (j : Fin 15) (hj : ‖p j‖ < b) : ∃ i, ix i = j := by
    obtain ⟨a, ha⟩ := hcover j hj
    obtain ⟨i, hi⟩ := hf.2 a
    exact ⟨i, by simpa [ix, hi] using ha⟩
  have hsepc : Separated qc 2 := fun i j hij => h.separated _ _ (hix.ne hij)
  have hneg (i : Fin 6) (hi : wordAHAHLL i = .A) :
      ∃ j, j ≠ i ∧ dist (qc i) (qc j) = 2 ∧
        ε * planeCross (qc i) (qc j - qc i) < 0 := by
    have hnorm := hAc i hi
    have hnot : ¬TouchesOuter p b (ix i) := by
      intro ht
      have hlow := touching_radius_ge_three_halves p b (ix i) hbhalf ht
      linarith [hnorm.2]
    have hnz : qc i ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hnorm
      linarith [hnorm.1]
    obtain ⟨hpos, hneg⟩ := two_sided_contacts_in_complete_inner_order p b hp
      h.twoSidedContacts qc ix (fun _ => rfl) hinnerc hcoverc i hnot hnz
    rcases heps with heps | heps
    · simpa [heps] using hneg
    · obtain ⟨j, hji, hc, hx⟩ := hpos
      exact ⟨j, hji, hc, by rw [heps]; linarith⟩
  have hcontacts := lifted_AHAHLL_forced_contact_split qc φ wordAHAHLL
    hsepc ε hframec (fun _ => rfl) hAc hHc hLc
    (hneg 0 (by decide)) (hneg 2 (by decide))
  obtain ⟨apos, hpos, hac, hhc, hatarget, hhblocker, hainj, hhinj, hadj⟩ := hselected
  let e : Fin 6 ≃ Fin 6 := Equiv.ofBijective f hf
  let ac : Fin 2 → Fin 6 := fun c => e.symm (apos c)
  let hc : Fin 2 → Fin 6 := fun c => e.symm (hpos c)
  have hfac (c : Fin 2) : f (ac c) = apos c := e.apply_symm_apply _
  have hfhc (c : Fin 2) : f (hc c) = hpos c := e.apply_symm_apply _
  have haclass (c : Fin 2) : wordAHAHLL (ac c) = .A := by
    rw [← hword, hfac]
    exact hac c
  have hhclass (c : Fin 2) : wordAHAHLL (hc c) = .H := by
    rw [← hword, hfhc]
    exact hhc c
  have haineq : ac 0 ≠ ac 1 := (e.symm.injective.comp hainj).ne (by decide)
  have hhineq : hc 0 ≠ hc 1 := (e.symm.injective.comp hhinj).ne (by decide)
  have hadjc (c : Fin 2) : cyclicNeighbor (ac c) (hc c) := by
    apply cyclic_neighbor_pullback f hf.1 hcycle
    simpa [hfac, hfhc] using hadj c
  have hstrict (c : Fin 2) : dist (qc (ac c)) (qc (hc c)) = 2 ∧
      ‖qc (ac c)‖ ^ 2 < ⟪qc (hc c), qc (ac c)⟫_ℝ := by
    rw [hqc, hqc, hfac, hfhc, hatarget, hhblocker]
    exact ⟨(hdata c).2.1, (hdata c).2.2.2.2.2.2.2⟩
  have hmatching := AHAHLL_two_adjacent_matching (ac 0) (ac 1) (hc 0) (hc 1)
    (haclass 0) (haclass 1) (hhclass 0) (hhclass 1)
    haineq hhineq (hadjc 0) (hadjc 1)
  have hstrict01 : dist (qc 0) (qc 1) = 2 ∧ ‖qc 0‖ ^ 2 < ⟪qc 1, qc 0⟫_ℝ := by
    rcases hmatching with ⟨ha0, hh0, _, _⟩ | ⟨_, _, ha1, hh1⟩
    · simpa [ha0, hh0] using hstrict 0
    · simpa [ha1, hh1] using hstrict 1
  have hstrict23 : dist (qc 2) (qc 3) = 2 ∧ ‖qc 2‖ ^ 2 < ⟪qc 3, qc 2⟫_ℝ := by
    rcases hmatching with ⟨_, _, ha1, hh1⟩ | ⟨ha0, hh0, _, _⟩
    · simpa [ha1, hh1] using hstrict 1
    · simpa [ha0, hh0] using hstrict 0
  exact ⟨ix, φ, ε, hix, heps, hinnerc, hcoverc, hframec, hsepc,
    hAc, hHc, hLc, hstrict01, hstrict23, hcontacts⟩

end CP15
