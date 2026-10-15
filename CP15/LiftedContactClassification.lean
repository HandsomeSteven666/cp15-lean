import CP15.LiftedSixGeometry

namespace CP15

/-- Contact classification in a canonical lifted frame, including cyclic
rotation across the polar branch cut and either orientation. -/
theorem lifted_AHAHLL_opposite_contact_classification
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ) (w : Fin 6 → M2Kind)
    (hsep : Separated q 2)
    (ε : ℝ) (hframe : LiftedSixFrame q φ ε)
    (hword : ∀ i, w i = wordAHAHLL i)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L → (3 / 2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (a j : Fin 6)
    (ha : w a = .A) (haj : a ≠ j)
    (hcontact : dist (q a) (q j) = 2)
    (hcross : ε * planeCross (q a) (q j - q a) < 0) :
    (a = 0 ∧ j = 5) ∨ (a = 2 ∧ (j = 0 ∨ j = 1)) := by
  have hnormA : 0 < ‖q a‖ := by
    have h := hA a ha
    linarith
  have harcshort := hframe.negative_cross_backward_arc_lt_pi a j haj hnormA (by
      have hsepij : 2 ≤ dist (q a) (q j) := by
        exact hsep a j haj
      have hqpos : 0 < ‖q j‖ := by
        by_contra hn
        have hz : q j = 0 := norm_eq_zero.mp (le_antisymm
          (le_of_not_gt hn) (norm_nonneg _))
        rw [hz] at hsepij
        have ha' := hA a ha
        have hdist : dist (q a) (0 : Plane) = ‖q a‖ := by simp [dist_eq_norm]
        rw [hdist] at hsepij
        linarith
      exact hqpos) (by
        have hcross' : ε * planeCross (q a) (q j - q a) < 0 := hcross
        exact hcross')
  have hA' (i : Fin 6) (hi : wordAHAHLL i = .A) :
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000 := by
    exact hA i ((hword i).trans hi)
  have hH' (i : Fin 6) (hi : wordAHAHLL i = .H) :
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000 := by
    exact hH i ((hword i).trans hi)
  have hL' (i : Fin 6) (hi : wordAHAHLL i = .L) :
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2 := by
    constructor
    · linarith [(hL i ((hword i).trans hi)).1]
    · exact (hL i ((hword i).trans hi)).2
  have hLweak (i : Fin 6) (hi : w i = .L) :
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2 := by
    have hh := hL i hi
    exact ⟨by linarith [hh.1], hh.2⟩
  have hgap (i : Fin 6) :
      ((classGapCost (wordAHAHLL i) (wordAHAHLL (i + 1)) : ℕ) : ℝ) *
        Real.pi / 1800 ≤ distinctSixGap φ i := by
    have hc := lifted_distinct_gap_cost q hsep φ ε hframe
      w hA hH hLweak i
    simpa [hword i, hword (i + 1)] using hc
  have hg0 : 49 * Real.pi / 180 ≤ distinctSixGap φ 0 := by
    have hh := hgap 0
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg1 : 49 * Real.pi / 180 ≤ distinctSixGap φ 1 := by
    have hh := hgap 1
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg2 : 49 * Real.pi / 180 ≤ distinctSixGap φ 2 := by
    have hh := hgap 2
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg3 : 53 * Real.pi / 180 ≤ distinctSixGap φ 3 := by
    have hh := hgap 3
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg4 : Real.pi / 3 ≤ distinctSixGap φ 4 := by
    have hh := hgap 4
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hsum := distinctSixGap_sum φ
  rw [Fin.sum_univ_six] at hsum
  have hsum' : distinctSixGap φ 0 + distinctSixGap φ 1 +
      distinctSixGap φ 2 + distinctSixGap φ 3 + distinctSixGap φ 4 +
      distinctSixGap φ 5 = 2 * Real.pi := by
    simpa [distinctSixGap] using hsum
  have hg5pi : distinctSixGap φ 5 < Real.pi := by
    nlinarith [hsum', hg0, hg1, hg2, hg3, hg4, Real.pi_pos]
  have hcos5 : Real.cos (polarArg (q 0) - polarArg (q 5)) =
      Real.cos (distinctSixGap φ 5) := by
    have hc := hframe.gap_cos 5
    have heq : polarArg (q 0) - polarArg (q 5) =
        -(polarArg (q 5) - polarArg (q 0)) := by ring
    rw [heq, Real.cos_neg]
    exact hc
  have hLfive : (7 / 5 : ℝ) ≤ ‖q 5‖ ∧ ‖q 5‖ ≤ 2 := by
    have hh := hL 5 (by simpa [hword 5, wordAHAHLL])
    exact ⟨by linarith [hh.1], hh.2⟩
  have hg5nonneg : 0 ≤ distinctSixGap φ 5 := hframe.gap_nonneg 5
  have hg5 : 59 * Real.pi / 150 < distinctSixGap φ 5 :=
    shared_AL_angle_gt_70_8 (q 0) (q 5) (distinctSixGap φ 5)
      (hA 0 (by simpa [hword 0, wordAHAHLL])).1
      (hA 0 (by simpa [hword 0, wordAHAHLL])).2
      hLfive.1 hLfive.2
      (by simpa [dist_comm] using hsep 0 5 (by decide))
       hcos5 hg5nonneg hg5pi.le
  have hwordA : a = 0 ∨ a = 2 := by
    have ha' : wordAHAHLL a = .A := by rw [← hword a]; exact ha
    fin_cases a <;> simp_all [wordAHAHLL]
  rcases hwordA with rfl | rfl
  · fin_cases j
    · exact False.elim (haj rfl)
    · have hbig : Real.pi < distinctForwardArc φ 1 0 := by
        have heq : distinctForwardArc φ 1 0 =
            distinctSixGap φ 1 + distinctSixGap φ 2 +
              distinctSixGap φ 3 + distinctSixGap φ 4 +
              distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg1, hg2, hg3, hg4, hg5, Real.pi_pos]
      have hs : distinctForwardArc φ 1 0 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have hbig : Real.pi < distinctForwardArc φ 2 0 := by
        have heq : distinctForwardArc φ 2 0 =
            distinctSixGap φ 2 + distinctSixGap φ 3 +
              distinctSixGap φ 4 + distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap]
        rw [heq]
        nlinarith [hg2, hg3, hg4, hg5, Real.pi_pos]
      have hs : distinctForwardArc φ 2 0 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have hbig : Real.pi < distinctForwardArc φ 3 0 := by
        have heq : distinctForwardArc φ 3 0 =
            distinctSixGap φ 3 + distinctSixGap φ 4 +
              distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap]
        rw [heq]
        nlinarith [hg3, hg4, hg5, Real.pi_pos]
      have hs : distinctForwardArc φ 3 0 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have h130 : 129 * Real.pi / 180 < distinctForwardArc φ 4 0 := by
        have heq : distinctForwardArc φ 4 0 =
            distinctSixGap φ 4 + distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg4, hg5, Real.pi_pos]
      have hlow := hL 4 (by norm_num [hword 4, wordAHAHLL])
      have hcos : Real.cos (distinctForwardArc φ 4 0) =
          Real.cos (polarArg (q 0) - polarArg (q 4)) := by
        have hc := hframe.arc_cos 4 0
        have heq : polarArg (q 4) - polarArg (q 0) =
            -(polarArg (q 0) - polarArg (q 4)) := by ring
        rw [heq, Real.cos_neg] at hc
        exact hc.symm
      have hangle := distinct_AL_contact_arc_lt_129 (q 0) (q 4)
        (distinctForwardArc φ 4 0) (hA 0 (by simpa [hword 0, wordAHAHLL])).1
        hlow.1 hlow.2 hcontact hcos
        (hframe.arc_range 4 0).1 harcshort.le
      exact False.elim (not_lt_of_ge h130.le hangle)
    · exact Or.inl ⟨rfl, rfl⟩
  · fin_cases j
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩
    · exact False.elim (haj rfl)
    · have hbig : Real.pi < distinctForwardArc φ 3 2 := by
        have heq : distinctForwardArc φ 3 2 =
            distinctSixGap φ 3 + distinctSixGap φ 4 + distinctSixGap φ 5 +
              distinctSixGap φ 0 + distinctSixGap φ 1 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg3, hg4, hg5, hg0, hg1, Real.pi_pos]
      have hs : distinctForwardArc φ 3 2 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have hbig : Real.pi < distinctForwardArc φ 4 2 := by
        have heq : distinctForwardArc φ 4 2 =
            distinctSixGap φ 4 + distinctSixGap φ 5 +
              distinctSixGap φ 0 + distinctSixGap φ 1 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg4, hg5, hg0, hg1, Real.pi_pos]
      have hs : distinctForwardArc φ 4 2 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have h129 : 129 * Real.pi / 180 < distinctForwardArc φ 5 2 := by
        have heq : distinctForwardArc φ 5 2 =
            distinctSixGap φ 5 + distinctSixGap φ 0 +
              distinctSixGap φ 1 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg5, hg0, hg1, Real.pi_pos]
      have hlow := hL 5 (by norm_num [hword 5, wordAHAHLL])
      have hcos : Real.cos (distinctForwardArc φ 5 2) =
          Real.cos (polarArg (q 2) - polarArg (q 5)) := by
        have hc := hframe.arc_cos 5 2
        have heq : polarArg (q 5) - polarArg (q 2) =
            -(polarArg (q 2) - polarArg (q 5)) := by ring
        rw [heq, Real.cos_neg] at hc
        exact hc.symm
      have hangle := distinct_AL_contact_arc_lt_129 (q 2) (q 5)
        (distinctForwardArc φ 5 2) (hA 2 (by simpa [hword 2, wordAHAHLL])).1
        hlow.1 hlow.2 hcontact hcos
        (hframe.arc_range 5 2).1 harcshort.le
      exact False.elim (not_lt_of_ge h129.le hangle)

/-- Once the two-sided contact theorem supplies negative-cross contacts,
the canonical cyclic order forces the final contact split: `A₀` contacts
`L₁`, while `A₁` contacts either `A₀` or `H₀`. -/
theorem lifted_AHAHLL_forced_contact_split
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ) (w : Fin 6 → M2Kind)
    (hsep : Separated q 2)
    (ε : ℝ) (hframe : LiftedSixFrame q φ ε)
    (hword : ∀ i, w i = wordAHAHLL i)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L → (3 / 2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (hneg0 : ∃ j, j ≠ 0 ∧ dist (q 0) (q j) = 2 ∧
      ε * planeCross (q 0) (q j - q 0) < 0)
    (hneg2 : ∃ j, j ≠ 2 ∧ dist (q 2) (q j) = 2 ∧
      ε * planeCross (q 2) (q j - q 2) < 0) :
    dist (q 0) (q 5) = 2 ∧
      (dist (q 2) (q 0) = 2 ∨ dist (q 2) (q 1) = 2) := by
  obtain ⟨j0, hj0, hc0, hcross0⟩ := hneg0
  have hclass0 := lifted_AHAHLL_opposite_contact_classification
    q φ w hsep ε hframe hword hA hH hL
    0 j0 (by simp [hword 0, wordAHAHLL]) hj0.symm hc0 hcross0
  have hcontact5 : j0 = 5 := by
    rcases hclass0 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · norm_num at h
  have hfirstContact : dist (q 0) (q 5) = 2 := by
    simpa [hcontact5] using hc0
  obtain ⟨j2, hj2, hc2, hcross2⟩ := hneg2
  have hclass2 := lifted_AHAHLL_opposite_contact_classification
    q φ w hsep ε hframe hword hA hH hL
    2 j2 (by simp [hword 2, wordAHAHLL]) hj2.symm hc2 hcross2
  have hlastContact : j2 = 0 ∨ j2 = 1 := by
    rcases hclass2 with ⟨h, _⟩ | ⟨_, h⟩
    · norm_num at h
    · exact h
  rcases hlastContact with hzero | hone
  · exact ⟨hfirstContact, Or.inl (by simpa [hzero] using hc2)⟩
  · exact ⟨hfirstContact, Or.inr (by simpa [hone] using hc2)⟩


end CP15

