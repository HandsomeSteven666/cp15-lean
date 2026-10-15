import CP15.M2K9DistinctCoreSum

namespace CP15

private theorem distinct_order_gap_lt_pi
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (i : Fin 6) : distinctSixGap φ i < Real.pi := by
  have hgap (j : Fin 6) :
      49 * Real.pi / 180 ≤ distinctSixGap φ j :=
    distinct_order_gap_at_least_49 q hsep φ hmono harg hfirst hlast
      w hA hH hL j
  have hsum := distinctSixGap_sum φ
  fin_cases i <;>
    rw [Fin.sum_univ_six] at hsum <;>
    simp [distinctSixGap] at hsum ⊢ <;>
    have hg0 := hgap 0 <;> have hg1 := hgap 1 <;>
    have hg2 := hgap 2 <;> have hg3 := hgap 3 <;>
    have hg4 := hgap 4 <;> have hg5 := hgap 5 <;>
    simp [distinctSixGap] at hg0 hg1 hg2 hg3 hg4 hg5 <;>
    nlinarith [Real.pi_pos]

private theorem distinct_predecessor_cos
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i) (a : Fin 6) :
    Real.cos (polarArg (q a) - polarArg (q (a - 1))) =
      Real.cos (distinctSixGap φ (a - 1)) := by
  have hsucc : (a - 1) + 1 = a := by
    fin_cases a <;> decide
  have hc := distinctSixGap_cos_lift q φ harg (a - 1)
  rw [hsucc] at hc
  calc
    Real.cos (polarArg (q a) - polarArg (q (a - 1))) =
        Real.cos (polarArg (q (a - 1)) - polarArg (q a)) := by
          rw [show polarArg (q a) - polarArg (q (a - 1)) =
            -(polarArg (q (a - 1)) - polarArg (q a)) by ring,
            Real.cos_neg]
    _ = Real.cos (distinctSixGap φ (a - 1)) := hc

/-- At a core center whose two cyclic neighbors have classes H and L,
the two incident angular gaps have combined size greater than 127 degrees.
The wrap-around predecessor and successor are handled by `Fin 6` arithmetic
and the lifted-gap cosine identity. -/
theorem distinct_core_flanking_gap_sum_gt_127
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (a : Fin 6) (ha : w a = .A)
    (hflank :
      (w (a + 1) = .H ∧ w (a - 1) = .L) ∨
      (w (a + 1) = .L ∧ w (a - 1) = .H)) :
    127 * Real.pi / 180 <
      distinctSixGap φ (a - 1) + distinctSixGap φ a := by
  have hneqNext : a ≠ a + 1 := by
    fin_cases a <;> decide
  have hneqPrev : a ≠ a - 1 := by
    fin_cases a <;> decide
  have hnextSep : 2 ≤ dist (q a) (q (a + 1)) := hsep a (a + 1) hneqNext
  have hprevSep : 2 ≤ dist (q a) (q (a - 1)) := by
    have hs := hsep (a - 1) a (Ne.symm hneqPrev)
    simpa [dist_comm] using hs
  have hcosNext := distinctSixGap_cos_lift q φ harg a
  have hcosPrev := distinct_predecessor_cos q φ harg a
  have hnextLo : 0 ≤ distinctSixGap φ a := by
    have hh := distinct_order_gap_at_least_49 q hsep φ hmono harg
      hfirst hlast w hA hH hL a
    exact le_trans (by positivity) hh
  have hprevLo : 0 ≤ distinctSixGap φ (a - 1) := by
    have hh := distinct_order_gap_at_least_49 q hsep φ hmono harg
      hfirst hlast w hA hH hL (a - 1)
    exact le_trans (by positivity) hh
  have hnextPi := distinct_order_gap_lt_pi q hsep φ hmono harg
    hfirst hlast w hA hH hL a
  have hprevPi := distinct_order_gap_lt_pi q hsep φ hmono harg
    hfirst hlast w hA hH hL (a - 1)
  rcases hflank with ⟨hnextH, hprevL⟩ | ⟨hnextL, hprevH⟩
  · have hcore := distinct_AH_AL_angle_sum_gt_127
      (q a) (q (a + 1)) (q (a - 1))
      (distinctSixGap φ a) (distinctSixGap φ (a - 1))
      (hA a ha).1 (hA a ha).2
      (hH (a + 1) hnextH).1 (hH (a + 1) hnextH).2
      (hL (a - 1) hprevL).1 (hL (a - 1) hprevL).2
      hnextSep hprevSep hcosNext hcosPrev hnextLo hnextPi.le
      hprevLo hprevPi.le
    linarith
  · have hcore := distinct_AH_AL_angle_sum_gt_127
      (q a) (q (a - 1)) (q (a + 1))
      (distinctSixGap φ (a - 1)) (distinctSixGap φ a)
      (hA a ha).1 (hA a ha).2
      (hH (a - 1) hprevH).1 (hH (a - 1) hprevH).2
      (hL (a + 1) hnextL).1 (hL (a + 1) hnextL).2
      hprevSep hnextSep hcosPrev hcosNext hprevLo hprevPi.le
      hnextLo hnextPi.le
    linarith [add_comm (distinctSixGap φ (a - 1))
      (distinctSixGap φ a)]

end CP15
