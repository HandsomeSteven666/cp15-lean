import CP15.CyclicInnerModel
import CP15.K10GapUniqueness
import CP15.AlternatingGeometry

namespace CP15

set_option maxHeartbeats 0

def occupiedEmptyCount (u : Fin 5 → Fin 10) (i : Fin 5) : ℕ :=
  if i = 4 then 10 + (u 0).val - (u 4).val - 1
  else (u (i + 1)).val - (u i).val - 1

/-- Five occupied gaps with exactly one empty gap between consecutive
occupied gaps must alternate around the ten-center boundary ring. -/
theorem occupiedEmptyCount_one_alternating
    (u : Fin 5 → Fin 10)
    (he : ∀ i, occupiedEmptyCount u i = 1) :
    ∃ a : Fin 2, ∀ i : Fin 5,
      (u i).val = a.val + 2 * i.val := by
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  simp only [occupiedEmptyCount] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have ha : (u 0).val < 2 := by
    have hbound := (u 4).isLt
    omega
  refine ⟨⟨(u 0).val, ha⟩, ?_⟩
  intro i
  fin_cases i <;> simp_all <;> omega

theorem occupiedEmptyCount_sum (u : Fin 5 → Fin 10) (hu : StrictMono u) :
    (∑ i, occupiedEmptyCount u i) = 5 := by
  have h01 := hu (show (0 : Fin 5) < 1 by decide)
  have h12 := hu (show (1 : Fin 5) < 2 by decide)
  have h23 := hu (show (2 : Fin 5) < 3 by decide)
  have h34 := hu (show (3 : Fin 5) < 4 by decide)
  simp only [Fin.lt_def] at h01 h12 h23 h34
  norm_num [Fin.sum_univ_five, occupiedEmptyCount]
  have h4 := (u 4).isLt
  omega

theorem occupiedEmptyCount_path (u : Fin 5 → Fin 10) (hu : StrictMono u)
    (i j : Fin 5) (hij : i ≠ j) :
    fiveArc (occupiedEmptyCount u) i (j - i) + (j - i).val - 1 =
      if i < j then (u j).val - (u i).val - 1
      else 10 + (u j).val - (u i).val - 1 := by
  have h01 := hu (show (0 : Fin 5) < 1 by decide)
  have h12 := hu (show (1 : Fin 5) < 2 by decide)
  have h23 := hu (show (2 : Fin 5) < 3 by decide)
  have h34 := hu (show (3 : Fin 5) < 4 by decide)
  simp only [Fin.lt_def] at h01 h12 h23 h34
  have h4 := (u 4).isLt
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp only [Fin.val_sub, Fin.val_neg]
  all_goals
    norm_num [fiveArc, occupiedEmptyCount, Finset.sum_range_succ,
      Fin.ofNat, Fin.sub, Fin.neg_def, Fin.val_neg, Fin.add,
      finFive_neg_one, finFive_neg_two, finFive_neg_three, finFive_neg_four] <;> omega

theorem fiveArc_cyclicAngleGap (φ : Fin 5 → ℝ) (i j : Fin 5) (hij : i ≠ j) :
    fiveArc (cyclicAngleGap φ) i (j - i) = φ j - φ i +
      if j < i then 2 * Real.pi else 0 := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp only [Fin.val_sub, Fin.val_neg]
  all_goals norm_num [fiveArc, cyclicAngleGap, Finset.sum_range_succ,
    Fin.ofNat, Fin.sub, Fin.neg_def, Fin.val_neg, Fin.add] <;> ring

/-- All intervening boundary gaps are counted, including the empty
path between consecutive occupied gaps. -/
theorem outer_span_forward (ψ : Fin 10 → ℝ) (α : ℝ)
    (hα : ∀ k, α ≤ cyclicAngleGap ψ k) (i j : Fin 10) (hij : i < j) :
    ((j.val - i.val - 1 : ℕ) : ℝ) * α ≤ ψ j - ψ i - cyclicAngleGap ψ i := by
  have h0 := hα 0; have h1 := hα 1; have h2 := hα 2
  have h3 := hα 3; have h4 := hα 4; have h5 := hα 5
  have h6 := hα 6; have h7 := hα 7; have h8 := hα 8
  norm_num [cyclicAngleGap] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num [cyclicAngleGap] <;> linarith

theorem outer_span_wrap (ψ : Fin 10 → ℝ) (α : ℝ)
    (hα : ∀ k, α ≤ cyclicAngleGap ψ k) (i j : Fin 10) (hji : j < i) :
    ((10 + j.val - i.val - 1 : ℕ) : ℝ) * α ≤
      ψ j + 2 * Real.pi - ψ i - cyclicAngleGap ψ i := by
  have h0 := hα 0; have h1 := hα 1; have h2 := hα 2
  have h3 := hα 3; have h4 := hα 4; have h5 := hα 5
  have h6 := hα 6; have h7 := hα 7; have h8 := hα 8; have h9 := hα 9
  norm_num [cyclicAngleGap] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  fin_cases i <;> fin_cases j <;> norm_num at hji
  all_goals norm_num [cyclicAngleGap] <;> linarith

/-- Convert actual lifted touching centers and their distinct occupied
outer gaps into the complete five-center cyclic model. No contact between
inner centers, double outer contact, or fixed gap size is assumed. -/
theorem occupied_gap_model (q : Fin 5 → Plane) (b : ℝ)
    (ψ : Fin 10 → ℝ) (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ)
    (hu : StrictMono u) (hsep : Separated q 2)
    (hr : ∀ i, ‖q i‖ ∈ Set.Icc (123 / 100 : ℝ) (9 / 4))
    (hα0 : 0 ≤ outerAlpha b) (hα : ∀ k, outerAlpha b ≤ cyclicAngleGap ψ k)
    (hphase : ∀ i, φ i = polarArg (q i) ∨ φ i = polarArg (q i) + 2 * Real.pi)
    (hleft : ∀ i, ψ (u i) + contactAngle b ‖q i‖ ≤ φ i)
    (hright : ∀ i, φ i ≤ ψ (u i) + cyclicAngleGap ψ (u i) - contactAngle b ‖q i‖)
    (hcost : 5 * (57588 / 100000 : ℝ) +
      (∑ i, max (57588 / 100000 : ℝ) (2 * contactAngle b ‖q i‖)) ≤ 2 * Real.pi) :
    CyclicInnerModel b (fun i => ‖q i‖) (occupiedEmptyCount u) (cyclicAngleGap φ) := by
  have hs (i j : Fin 5) (hij : i ≠ j) :
      contactAngle b ‖q i‖ + contactAngle b ‖q j‖ +
        ((fiveArc (occupiedEmptyCount u) i (j - i) + (j - i).val - 1 : ℕ) : ℝ) *
          outerAlpha b ≤ fiveArc (cyclicAngleGap φ) i (j - i) := by
    rw [occupiedEmptyCount_path u hu i j hij, fiveArc_cyclicAngleGap φ i j hij]
    by_cases hlt : i < j
    · have hn : ¬j < i := not_lt_of_ge hlt.le
      rw [if_pos hlt, if_neg hn, add_zero]
      have hh := outer_span_forward ψ (outerAlpha b) hα (u i) (u j) (hu hlt)
      linarith [hleft j, hright i]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      rw [if_neg hlt, if_pos hji]
      have hh := outer_span_wrap ψ (outerAlpha b) hα (u i) (u j) (hu hji)
      linarith [hleft j, hright i]
  have hs' (i d : Fin 5) (hd : d ≠ 0) :
      contactAngle b ‖q i‖ + contactAngle b ‖q (i + d)‖ +
        ((fiveArc (occupiedEmptyCount u) i d + d.val - 1 : ℕ) : ℝ) * outerAlpha b ≤
          fiveArc (cyclicAngleGap φ) i d := by
    have hne : i ≠ i + d := by
      intro hh
      have hc : (0 : Fin 5) = d := add_left_cancel (show i + 0 = i + d by simpa using hh)
      exact hd hc.symm
    have heq : i + d - i = d := by abel
    simpa only [heq] using hs i (i + d) hne
  have hg (i d : Fin 5) (hd : d ≠ 0) : 0 ≤ fiveArc (cyclicAngleGap φ) i d := by
    have hh := hs' i d hd
    have hc0 := Real.arccos_nonneg (contactCos b ‖q i‖)
    have hc1 := Real.arccos_nonneg (contactCos b ‖q (i + d)‖)
    have hn : (0 : ℝ) ≤ ((fiveArc (occupiedEmptyCount u) i d + d.val - 1 : ℕ) : ℝ) := by positivity
    have hp := mul_nonneg hn hα0
    change 0 ≤ contactAngle b ‖q i‖ at hc0
    change 0 ≤ contactAngle b ‖q (i + d)‖ at hc1
    linarith
  refine ⟨hr, occupiedEmptyCount_sum u hu, ?_, cyclicAngleGap_sum φ, ?_, hs', hcost⟩
  · intro i
    simpa [fiveArc] using hg i 1 (by decide)
  · intro i d hd
    have hne : i ≠ i + d := by
      intro hh
      have hc : (0 : Fin 5) = d := add_left_cancel (show i + 0 = i + d by simpa using hh)
      exact hd hc.symm
    apply directed_clearance_angle_lower (q i) (q (i + d)) _
      (by linarith [(hr i).1]) (by linarith [(hr (i + d)).1])
      (hsep i (i + d) hne) (hg i d hd)
    have heq : i + d - i = d := by abel
    have ha := fiveArc_cyclicAngleGap φ i (i + d) hne
    rw [heq] at ha
    rw [ha]
    have hc := cos_diff_of_two_pi_lifts _ _ _ _ (hphase i) (hphase (i + d))
    by_cases hl : i + d < i
    · rw [if_pos hl, Real.cos_add_two_pi, ← Real.cos_neg (φ (i + d) - φ i)]
      convert hc using 1 <;> congr 1 <;> ring
    · rw [if_neg hl, add_zero, ← Real.cos_neg (φ (i + d) - φ i)]
      convert hc using 1 <;> congr 1 <;> ring

end CP15
