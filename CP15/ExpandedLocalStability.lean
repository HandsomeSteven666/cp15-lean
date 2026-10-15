import CP15.ExpandedLocalLinearization
import CP15.LocalAngularStability

namespace CP15

private theorem expanded_max_margin_of_two_linearizations (g d σ x e : ℝ)
    (he : 0 ≤ e)
    (hg : |g - σ - (81 / 100 : ℝ) * x| ≤ (8 / 100 : ℝ) * e)
    (hd : |d - σ + (43 / 100 : ℝ) * x| ≤ (8 / 100 : ℝ) * e) :
    (43 / 100 : ℝ) * |x| - (8 / 100 : ℝ) * e ≤ max g d - σ := by
  have hgl := (abs_le.mp hg).1
  have hdl := (abs_le.mp hd).1
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [le_max_left g d]
  · rw [abs_of_nonpos (le_of_not_ge hx)]
    linarith [le_max_right g d]

/-- Actual angle functions, rather than a postulated linearized estimate,
give an L1 margin throughout the closed local cube. The sole reference
identity is explicit; it will be checked for the exact candidate constants.
The direct maximum estimate loses `0.16`, yielding `0.012 = 3/250`. -/
theorem expanded_angular_stability (b α r₀ : ℝ) (r : Fin 5 → ℝ)
    (hblo : (35213 / 10000 : ℝ) ≤ b) (hbhi : b ≤ 35214 / 10000)
    (h₀ : r₀ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr : ∀ i, r i ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hbalance : α + 2 * contactAngle b r₀ = contactAngle r₀ r₀) :
    (3 / 250 : ℝ) * (∑ i, |r i - r₀|) ≤
      localAngularCost b α r - 5 * (α + 2 * contactAngle b r₀) := by
  let t : Fin 5 → ℝ := fun i => r i - r₀
  let σ : ℝ := α + 2 * contactAngle b r₀
  have hpoint (i : Fin 5) :
      (43 / 100 : ℝ) * |fiveAdjacentSum t i| -
        (8 / 100 : ℝ) * fiveAdjacentSum (fun j => |t j|) i ≤
      max (α + contactAngle b (r i) + contactAngle b (r (i + 1)))
        (contactAngle (r (i + 1)) (r i)) - σ := by
    apply expanded_max_margin_of_two_linearizations
    · dsimp [fiveAdjacentSum]
      positivity
    · have h1 := expanded_outer_angle_linearization b (r i) r₀ hblo hbhi (hr i) h₀
      have h2 := expanded_outer_angle_linearization b (r (i + 1)) r₀
        hblo hbhi (hr (i + 1)) h₀
      have ha := abs_add_le
        (contactAngle b (r i) - contactAngle b r₀ - (81 / 100 : ℝ) * t i)
        (contactAngle b (r (i + 1)) - contactAngle b r₀ -
          (81 / 100 : ℝ) * t (i + 1))
      have heq :
          (contactAngle b (r i) - contactAngle b r₀ - (81 / 100 : ℝ) * t i) +
          (contactAngle b (r (i + 1)) - contactAngle b r₀ -
            (81 / 100 : ℝ) * t (i + 1)) =
          α + contactAngle b (r i) + contactAngle b (r (i + 1)) - σ -
            (81 / 100 : ℝ) * fiveAdjacentSum t i := by
        dsimp [σ, fiveAdjacentSum]
        ring
      rw [heq] at ha
      dsimp [fiveAdjacentSum, t] at *
      linarith
    · have hpair := expanded_pair_angle_linearization (r i) (r (i + 1)) r₀
        (hr i) (hr (i + 1)) h₀
      dsimp [σ, fiveAdjacentSum, t]
      rw [hbalance]
      exact hpair
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hsum :
      (43 / 100 : ℝ) * (∑ i, |fiveAdjacentSum t i|) -
        (8 / 100 : ℝ) * (∑ i, fiveAdjacentSum (fun j => |t j|) i) ≤
      localAngularCost b α r - 5 * σ := by
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
      localAngularCost] using hs
  rw [five_adjacent_sum_total] at hsum
  have hodd := five_adjacent_sum_l1_lower t
  dsimp [t, σ] at hsum hodd
  linarith

end CP15
