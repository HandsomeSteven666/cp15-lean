import CP15.Definitions

namespace CP15

noncomputable def fiveAdjacentSum (t : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  t i + t (i + 1)

/-- The inverse of the adjacent-sum operator on the odd five-cycle.
There is no alternating null direction, unlike an even cycle. -/
theorem five_adjacent_sum_inverse (t : Fin 5 → ℝ) (i : Fin 5) :
    2 * t i = fiveAdjacentSum t i - fiveAdjacentSum t (i + 1) +
      fiveAdjacentSum t (i + 2) - fiveAdjacentSum t (i + 3) +
      fiveAdjacentSum t (i + 4) := by
  fin_cases i <;> simp [fiveAdjacentSum] <;> ring

private theorem abs_alternating_five_le (a b c d e : ℝ) :
    |a - b + c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 : |a - b| ≤ |a| + |b| := by
    simpa [sub_eq_add_neg] using abs_add_le a (-b)
  have h2 := abs_add_le (a - b) c
  have h3 : |a - b + c - d| ≤ |a - b + c| + |d| := by
    simpa [sub_eq_add_neg] using abs_add_le (a - b + c) (-d)
  have h4 := abs_add_le (a - b + c - d) e
  linarith

theorem five_adjacent_sum_l1_lower (t : Fin 5 → ℝ) :
    (2 / 5 : ℝ) * (∑ i, |t i|) ≤ ∑ i, |fiveAdjacentSum t i| := by
  have hb (i : Fin 5) : 2 * |t i| ≤ ∑ j, |fiveAdjacentSum t j| := by
    have h := abs_alternating_five_le (fiveAdjacentSum t i)
      (fiveAdjacentSum t (i + 1)) (fiveAdjacentSum t (i + 2))
      (fiveAdjacentSum t (i + 3)) (fiveAdjacentSum t (i + 4))
    rw [← five_adjacent_sum_inverse t i, abs_mul] at h
    norm_num at h
    convert h using 1
    fin_cases i <;> norm_num [Fin.sum_univ_five] <;> ring
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  norm_num at hs
  linarith

theorem five_adjacent_sum_total (t : Fin 5 → ℝ) :
    (∑ i, fiveAdjacentSum t i) = 2 * (∑ i, t i) := by
  simp [fiveAdjacentSum, Fin.sum_univ_five]
  ring

/-- Exact scalar inequality in the final local stability argument. -/
theorem local_piecewise_coercivity (x : ℝ) :
    (43 / 100 : ℝ) * |x| ≤
      (81 / 100 : ℝ) * x + (124 / 100 : ℝ) * max 0 (-x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left (by linarith)]
    linarith
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    rw [abs_of_nonpos hx', max_eq_right (by linarith)]
    ring_nf
    exact le_rfl

/-- This is the algebraic conclusion of the analytic local estimate.
The estimate is an explicit premise: derivative bounds and the mean-value
argument still must be proved for the actual angle functions. -/
theorem local_margin_of_linearized_estimate (t : Fin 5 → ℝ) (excess : ℝ)
    (hestimate :
      (81 / 100 : ℝ) * (∑ i, fiveAdjacentSum t i) +
      (124 / 100 : ℝ) * (∑ i, max 0 (-fiveAdjacentSum t i)) -
      (1 / 10 : ℝ) * (∑ i, |t i|) ≤ excess) :
    (9 / 125 : ℝ) * (∑ i, |t i|) ≤ excess := by
  have hpoint := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => local_piecewise_coercivity (fiveAdjacentSum t i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hpoint
  have hodd := five_adjacent_sum_l1_lower t
  nlinarith

/-- The strict L1 margin has a unique zero vector. -/
theorem zero_vector_of_local_margin (t : Fin 5 → ℝ) (excess : ℝ)
    (hmargin : (9 / 125 : ℝ) * (∑ i, |t i|) ≤ excess)
    (hexcess : excess ≤ 0) : ∀ i, t i = 0 := by
  have hsum0 : (∑ i, |t i|) = 0 := by
    have hnonneg := Finset.sum_nonneg (s := Finset.univ)
      (fun i _ => abs_nonneg (t i))
    linarith
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => abs_nonneg (t i))).1 hsum0
  intro i
  exact abs_eq_zero.mp (hterms i (Finset.mem_univ i))

end CP15
