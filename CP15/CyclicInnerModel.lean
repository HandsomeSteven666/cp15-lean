import CP15.LocalAlternatingClosed
import CP15.DifferenceCertificate

namespace CP15

set_option maxHeartbeats 0

theorem finFive_neg_one : (-1 : Fin 5) = 4 := by decide
theorem finFive_neg_two : (-2 : Fin 5) = 3 := by decide
theorem finFive_neg_three : (-3 : Fin 5) = 2 := by decide
theorem finFive_neg_four : (-4 : Fin 5) = 1 := by decide

/-- A directed path of fewer than five cyclic edges. The domain of its
length is Fin 5; length zero denotes the empty path. -/
def fiveArc {A : Type*} [AddCommMonoid A] (g : Fin 5 → A) (i d : Fin 5) : A :=
  ∑ k ∈ Finset.range d.val, g (i + Fin.ofNat 5 k)

theorem fiveArc_rotate {A : Type*} [AddCommMonoid A] (g : Fin 5 → A)
    (a i d : Fin 5) :
    fiveArc (fun j => g (j + a)) i d = fiveArc g (i + a) d := by
  unfold fiveArc
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ac_rfl

theorem five_reflected_path_index : ∀ a i d k : Fin 5, k < d →
    a - (i + Fin.ofNat 5 (d.val - 1 - k.val)) - 1 = a - i - d + k := by
  decide +kernel

theorem fiveArc_reflect {A : Type*} [AddCommMonoid A] (g : Fin 5 → A)
    (a i d : Fin 5) :
    fiveArc (fun j => g (a - j - 1)) i d = fiveArc g (a - i - d) d := by
  unfold fiveArc
  rw [← Finset.sum_range_reflect (fun k => g (a - (i + Fin.ofNat 5 k) - 1)) d.val]
  apply Finset.sum_congr rfl
  intro k hk
  have hk5 : k < 5 := (Finset.mem_range.mp hk).trans d.isLt
  have hh := five_reflected_path_index a i d ⟨k, hk5⟩ (Finset.mem_range.mp hk)
  have hkCast : Fin.ofNat 5 k = (⟨k, hk5⟩ : Fin 5) :=
    Fin.ofNat_val_eq_self ⟨k, hk5⟩
  congr 1
  rw [hkCast]
  exact hh

theorem five_sum_rotate {A : Type*} [AddCommMonoid A] (g : Fin 5 → A) (a : Fin 5) :
    (∑ i, g (i + a)) = ∑ i, g i := by
  fin_cases a <;> norm_num [Fin.sum_univ_five, Fin.add] <;> abel

theorem five_sum_reflect {A : Type*} [AddCommMonoid A] (g : Fin 5 → A) (a : Fin 5) :
    (∑ i, g (a - i)) = ∑ i, g i := by
  fin_cases a <;> norm_num [Fin.sum_univ_five, Fin.sub, Fin.neg_def, Fin.val_neg, Fin.add,
    finFive_neg_one, finFive_neg_two, finFive_neg_three, finFive_neg_four] <;> abel

theorem five_sum_reflect_edges {A : Type*} [AddCommMonoid A] (g : Fin 5 → A) (a : Fin 5) :
    (∑ i, g (a - i - 1)) = ∑ i, g i := by
  convert five_sum_reflect g (a - 1) using 1
  congr 1
  funext i
  abel

/-- Necessary scalar inequalities derived from five distinct occupied
outer gaps. The empty-gap counts are counted between successive occupied
gaps. All pair clearances and both directed paths are retained. -/
structure CyclicInnerModel (b : ℝ) (r : Fin 5 → ℝ)
    (empty : Fin 5 → ℕ) (g : Fin 5 → ℝ) : Prop where
  radius : ∀ i, r i ∈ Set.Icc (123 / 100 : ℝ) (9 / 4)
  empty_sum : (∑ i, empty i) = 5
  gap_nonneg : ∀ i, 0 ≤ g i
  gap_sum : (∑ i, g i) = 2 * Real.pi
  pair : ∀ i d, d ≠ 0 → contactAngle (r i) (r (i + d)) ≤ fiveArc g i d
  support : ∀ i d, d ≠ 0 →
    contactAngle b (r i) + contactAngle b (r (i + d)) +
      ((fiveArc empty i d + d.val - 1 : ℕ) : ℝ) * outerAlpha b ≤ fiveArc g i d
  outer_cost : 5 * (57588 / 100000 : ℝ) +
    (∑ i, max (57588 / 100000 : ℝ) (2 * contactAngle b (r i))) ≤ 2 * Real.pi

theorem CyclicInnerModel.rotate {b : ℝ} {r : Fin 5 → ℝ}
    {e : Fin 5 → ℕ} {g : Fin 5 → ℝ} (h : CyclicInnerModel b r e g) (a : Fin 5) :
    CyclicInnerModel b (fun i => r (i + a)) (fun i => e (i + a)) (fun i => g (i + a)) := by
  refine ⟨fun i => h.radius (i + a), ?_, fun i => h.gap_nonneg (i + a), ?_, ?_, ?_, ?_⟩
  · rw [five_sum_rotate]
    exact h.empty_sum
  · rw [five_sum_rotate]
    exact h.gap_sum
  · intro i d hd
    rw [fiveArc_rotate]
    convert h.pair (i + a) d hd using 1 <;> congr 2 <;> ac_rfl
  · intro i d hd
    rw [fiveArc_rotate, fiveArc_rotate]
    convert h.support (i + a) d hd using 1 <;> congr 2 <;> ac_rfl
  · simpa only [five_sum_rotate (fun i => max (57588 / 100000 : ℝ)
      (2 * contactAngle b (r i))) a] using h.outer_cost

theorem CyclicInnerModel.reflect {b : ℝ} {r : Fin 5 → ℝ}
    {e : Fin 5 → ℕ} {g : Fin 5 → ℝ} (h : CyclicInnerModel b r e g) (a : Fin 5) :
    CyclicInnerModel b (fun i => r (a - i))
      (fun i => e (a - i - 1)) (fun i => g (a - i - 1)) := by
  refine ⟨fun i => h.radius (a - i), ?_, fun i => h.gap_nonneg (a - i - 1), ?_, ?_, ?_, ?_⟩
  · rw [five_sum_reflect_edges]
    exact h.empty_sum
  · rw [five_sum_reflect_edges]
    exact h.gap_sum
  · intro i d hd
    rw [fiveArc_reflect]
    have heq : a - (i + d) = a - i - d := by abel
    have heq' : a - i - d + d = a - i := by abel
    rw [heq, contactAngle_comm]
    simpa only [heq'] using h.pair (a - i - d) d hd
  · intro i d hd
    rw [fiveArc_reflect, fiveArc_reflect]
    have heq : a - (i + d) = a - i - d := by abel
    have heq' : a - i - d + d = a - i := by abel
    rw [heq]
    have hs := h.support (a - i - d) d hd
    rw [heq'] at hs
    linarith
  · simpa only [five_sum_reflect (fun i => max (57588 / 100000 : ℝ)
      (2 * contactAngle b (r i))) a] using h.outer_cost

/-- At alternating occupancy, the actual scalar model supplies the
necessary cost required by the analytic local closure. -/
theorem CyclicInnerModel.alternating_cost {b : ℝ} {r : Fin 5 → ℝ}
    {g : Fin 5 → ℝ} (h : CyclicInnerModel b r (fun _ => 1) g) :
    localAngularCost b (outerAlpha b) r ≤ 2 * Real.pi := by
  have hp (i : Fin 5) :
      max (outerAlpha b + contactAngle b (r i) + contactAngle b (r (i + 1)))
        (contactAngle (r (i + 1)) (r i)) ≤ g i := by
    have hs := h.support i 1 (by decide)
    have hc := h.pair i 1 (by decide)
    norm_num [fiveArc] at hs hc
    rw [contactAngle_comm] at hc
    exact max_le (by linarith) hc
  simpa only [localAngularCost, h.gap_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)

/-- Prefix potentials put a directed cyclic path in the ordinary
difference-constraint form. A wrapped path retains exactly one turn. -/
theorem fiveArc_as_difference (g : Fin 5 → ℝ) (i j : Fin 5) (hij : i ≠ j) :
    fiveArc g i (j - i) = fiveArc g 0 j - fiveArc g 0 i +
      if j < i then (∑ k, g k) else 0 := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp only [Fin.val_sub, Fin.val_neg]
  all_goals norm_num [fiveArc, Finset.sum_range_succ, Fin.sum_univ_five,
    Fin.ofNat, Fin.sub, Fin.neg_def, Fin.val_neg, Fin.add,
    finFive_neg_one, finFive_neg_two, finFive_neg_three, finFive_neg_four] <;> ring

end CP15
