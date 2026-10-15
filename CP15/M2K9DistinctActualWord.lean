import CP15.M2K9DistinctCoreExclusion
import CP15.M2K9DistinctGeometry

namespace CP15

open scoped InnerProductSpace
set_option maxHeartbeats 0

private theorem distinct_add_cyclicNeighbor
    (k i j : Fin 6) (h : cyclicNeighbor i j) :
    cyclicNeighbor (i + k) (j + k) := by
  have hadd (x : Fin 6) : (x + 1) + k = (x + k) + 1 := by
    fin_cases x <;> fin_cases k <;> decide
  rcases h with hj | hi
  · left
    rw [hj]
    exact hadd i
  · right
    rw [hi]
    exact hadd j

private theorem distinct_sub_succ_right (k i : Fin 6) :
    k - i = (k - (i + 1)) + 1 := by
  fin_cases k <;> fin_cases i <;> decide

private theorem distinct_add_right_injective (k : Fin 6) :
    Function.Injective (fun i : Fin 6 => i + k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at *

private theorem distinct_sub_left_injective (k : Fin 6) :
    Function.Injective (fun i : Fin 6 => k - i) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at *

private theorem distinct_sub_add_cancel (i k : Fin 6) :
    (i - k) + k = i := by
  fin_cases i <;> fin_cases k <;> decide

private theorem distinct_sub_sub_cancel (i k : Fin 6) :
    i - (i - k) = k := by
  fin_cases i <;> fin_cases k <;> decide

private theorem distinct_sub_succ_eq (j k : Fin 6) :
    (j + 1) - k = (j - k) + 1 := by
  fin_cases j <;> fin_cases k <;> decide

private theorem distinct_reverse_succ_eq (j k : Fin 6) :
    k - (j + 1) + 1 = k - j := by
  fin_cases j <;> fin_cases k <;> decide

/-- Every dihedral class-word witness gives an explicit cyclic reindexing
of the actual sorted centers, with its orientation recorded. -/
theorem distinct_AHAHLL_cyclic_reindex
    (w : Fin 6 → M2Kind)
    (horbit : dihedralEquivalent w wordAHAHLL) :
    ∃ f : Fin 6 → Fin 6,
      Function.Bijective f ∧
      (∀ j, w (f j) = wordAHAHLL j) ∧
      ((∀ j, f (j + 1) = f j + 1) ∨
        (∀ j, f (j + 1) + 1 = f j)) := by
  rcases horbit with ⟨k, hforward | hreverse⟩
  · let f : Fin 6 → Fin 6 := fun j => j - k
    have hinj : Function.Injective f := by
      intro i j hij
      have hi := congrArg (fun x : Fin 6 => x + k) hij
      simpa [f, distinct_sub_add_cancel] using hi
    have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
    refine ⟨f, ⟨hinj, hsurj⟩, ?_, Or.inl ?_⟩
    · intro j
      calc
        w (f j) = wordAHAHLL (f j + k) := hforward (f j)
        _ = wordAHAHLL j := by simp [f, distinct_sub_add_cancel]
    · intro j
      exact distinct_sub_succ_eq j k
  · let f : Fin 6 → Fin 6 := fun j => k - j
    have hinj : Function.Injective f := by
      intro i j hij
      have hi := congrArg (fun x : Fin 6 => k - x) hij
      simpa [f, distinct_sub_sub_cancel] using hi
    have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
    refine ⟨f, ⟨hinj, hsurj⟩, ?_, Or.inr ?_⟩
    · intro j
      calc
        w (f j) = wordAHAHLL (k - f j) := hreverse (f j)
        _ = wordAHAHLL j := by simp [f, distinct_sub_sub_cancel]
    · intro j
      exact distinct_reverse_succ_eq j k

private theorem distinct_sub_cyclicNeighbor
    (k i j : Fin 6) (h : cyclicNeighbor i j) :
    cyclicNeighbor (k - i) (k - j) := by
  rcases h with hj | hi
  · right
    rw [hj]
    exact distinct_sub_succ_right k i
  · left
    rw [hi]
    exact distinct_sub_succ_right k j

private theorem AHAHLL_one_adjacent_AH
    (a h : Fin 6)
    (ha : wordAHAHLL a = .A) (hh : wordAHAHLL h = .H)
    (hadj : cyclicNeighbor a h) :
    (a = 0 ∧ h = 1) ∨ (a = 2 ∧ h = 1) ∨ (a = 2 ∧ h = 3) := by
  fin_cases a <;> fin_cases h <;>
    norm_num [wordAHAHLL, cyclicNeighbor] at *

theorem AHAHLL_two_adjacent_matching
    (a0 a1 h0 h1 : Fin 6)
    (ha0 : wordAHAHLL a0 = .A) (ha1 : wordAHAHLL a1 = .A)
    (hh0 : wordAHAHLL h0 = .H) (hh1 : wordAHAHLL h1 = .H)
    (haNe : a0 ≠ a1) (hhNe : h0 ≠ h1)
    (hadj0 : cyclicNeighbor a0 h0) (hadj1 : cyclicNeighbor a1 h1) :
    (a0 = 0 ∧ h0 = 1 ∧ a1 = 2 ∧ h1 = 3) ∨
      (a0 = 2 ∧ h0 = 3 ∧ a1 = 0 ∧ h1 = 1) := by
  fin_cases a0 <;> fin_cases a1 <;>
    fin_cases h0 <;> fin_cases h1 <;>
      norm_num [wordAHAHLL, cyclicNeighbor] at *

/-- From the actual two targets and their distinct selected blockers, the
ordered six touching centers have the AHAHLL class word up to rotation and
reversal. The witness also retains the actual target/blocker indices in
the ordered list, so the word conclusion is connected back to the packing. -/
theorem distinct_k9_actual_AHAHLL_word
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i →
      ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hK9 : (boundarySet p b).card = 9)
    (hm2 : (nonOuterIndices p b).card = 2)
    (target blocker outer : Fin 2 → Fin 15)
    (htarget : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c))
    (hdata : ∀ c, blocker c ≠ target c ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
      outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
      dist (p (blocker c)) (p (outer c)) = 2 ∧
      ‖p (target c)‖ ^ 2 <
        ⟪p (blocker c), p (target c)⟫_ℝ)
    (hblocker_ne : blocker 0 ≠ blocker 1) :
    ∃ q : Fin 6 → Plane, ∃ φ : Fin 6 → ℝ,
      ∃ w : Fin 6 → M2Kind,
        Separated q 2 ∧ StrictMono φ ∧
        (∀ i, polarArg (q i) = φ i) ∧
        -Real.pi < φ 0 ∧ φ 5 ≤ Real.pi ∧
        classCount w .A = 2 ∧ classCount w .H = 2 ∧
        classCount w .L = 2 ∧
        (∀ i, w i = .A →
          (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000) ∧
        (∀ i, w i = .H →
          (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000) ∧
        (∀ i, w i = .L →
          (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2) ∧
        (∃ apos hpos : Fin 2 → Fin 6,
          (∀ c, w (apos c) = .A) ∧
          (∀ c, w (hpos c) = .H) ∧
          (∀ c, q (apos c) = p (target c)) ∧
          (∀ c, q (hpos c) = p (blocker c)) ∧
          Function.Injective apos ∧ Function.Injective hpos ∧
          (∀ c, cyclicNeighbor (apos c) (hpos c))) ∧
        dihedralEquivalent w wordAHAHLL ∧
        (∃ ix : Fin 6 → Fin 15,
          Function.Injective ix ∧ (∀ i, q i = p (ix i)) ∧
          (∀ i, ‖p (ix i)‖ < b) ∧
          (∀ j, ‖p j‖ < b → ∃ i, ix i = j)) := by
  obtain ⟨q, φ, w, hsep, hmono, harg, hfirst, hlast,
      hAcount, hHcount, hLcount, hArad, hHrad, hLrad,
      hselected, hmatch, hbudget, hindex⟩ :=
    distinct_k9_actual_six_order_budget p b hb hbB hpack hD hFcap
      hFsmall hblock hK9 hm2 target blocker outer htarget hno hdata
      hblocker_ne
  have horbit := distinct_six_order_word_AHAHLL q hsep φ hmono harg
    hfirst hlast w hAcount hHcount hLcount hArad hHrad hLrad hmatch
    hbudget
  exact ⟨q, φ, w, hsep, hmono, harg, hfirst, hlast, hAcount, hHcount,
    hLcount, hArad, hHrad, hLrad, hselected, horbit, hindex⟩

/-- The actual selected distinct blockers occupy the unique adjacent A-H
matching in the AHAHLL cyclic word. The statement keeps both possible
orientation conventions explicit as exact `Fin 6` arithmetic. -/
theorem distinct_AHAHLL_selected_matching_normalization
    (w : Fin 6 → M2Kind) (apos hpos : Fin 2 → Fin 6)
    (horbit : dihedralEquivalent w wordAHAHLL)
    (ha : ∀ c, w (apos c) = .A)
    (hh : ∀ c, w (hpos c) = .H)
    (hainj : Function.Injective apos)
    (hhinj : Function.Injective hpos)
    (hadj : ∀ c, cyclicNeighbor (apos c) (hpos c)) :
    (∃ k : Fin 6,
      (apos 0 + k = 0 ∧ hpos 0 + k = 1 ∧
        apos 1 + k = 2 ∧ hpos 1 + k = 3) ∨
      (apos 0 + k = 2 ∧ hpos 0 + k = 3 ∧
        apos 1 + k = 0 ∧ hpos 1 + k = 1)) ∨
    (∃ k : Fin 6,
      (k - apos 0 = 0 ∧ k - hpos 0 = 1 ∧
        k - apos 1 = 2 ∧ k - hpos 1 = 3) ∨
      (k - apos 0 = 2 ∧ k - hpos 0 = 3 ∧
        k - apos 1 = 0 ∧ k - hpos 1 = 1)) := by
  rcases horbit with ⟨k, hforward | hreverse⟩
  · left
    have hcanA (c : Fin 2) : wordAHAHLL (apos c + k) = .A := by
      calc
        wordAHAHLL (apos c + k) = w (apos c) := (hforward (apos c)).symm
        _ = .A := ha c
    have hcanH (c : Fin 2) : wordAHAHLL (hpos c + k) = .H := by
      calc
        wordAHAHLL (hpos c + k) = w (hpos c) := (hforward (hpos c)).symm
        _ = .H := hh c
    have hdiffA : apos 0 + k ≠ apos 1 + k :=
      (distinct_add_right_injective k).ne (hainj.ne (by decide))
    have hdiffH : hpos 0 + k ≠ hpos 1 + k :=
      (distinct_add_right_injective k).ne (hhinj.ne (by decide))
    have hadj0 := distinct_add_cyclicNeighbor k (apos 0) (hpos 0) (hadj 0)
    have hadj1 := distinct_add_cyclicNeighbor k (apos 1) (hpos 1) (hadj 1)
    have hforced := AHAHLL_two_adjacent_matching
      (apos 0 + k) (apos 1 + k) (hpos 0 + k) (hpos 1 + k)
      (hcanA 0) (hcanA 1) (hcanH 0) (hcanH 1)
      hdiffA hdiffH hadj0 hadj1
    exact ⟨k, hforced⟩
  · right
    have hcanA (c : Fin 2) : wordAHAHLL (k - apos c) = .A := by
      calc
        wordAHAHLL (k - apos c) = w (apos c) := (hreverse (apos c)).symm
        _ = .A := ha c
    have hcanH (c : Fin 2) : wordAHAHLL (k - hpos c) = .H := by
      calc
        wordAHAHLL (k - hpos c) = w (hpos c) := (hreverse (hpos c)).symm
        _ = .H := hh c
    have hdiffA : k - apos 0 ≠ k - apos 1 :=
      (distinct_sub_left_injective k).ne (hainj.ne (by decide))
    have hdiffH : k - hpos 0 ≠ k - hpos 1 :=
      (distinct_sub_left_injective k).ne (hhinj.ne (by decide))
    have hadj0 := distinct_sub_cyclicNeighbor k (apos 0) (hpos 0) (hadj 0)
    have hadj1 := distinct_sub_cyclicNeighbor k (apos 1) (hpos 1) (hadj 1)
    have hforced := AHAHLL_two_adjacent_matching
      (k - apos 0) (k - apos 1) (k - hpos 0) (k - hpos 1)
      (hcanA 0) (hcanA 1) (hcanH 0) (hcanH 1)
      hdiffA hdiffH hadj0 hadj1
    exact ⟨k, hforced⟩

end CP15
