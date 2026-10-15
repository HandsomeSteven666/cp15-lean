import CP15.LocalAngleLinearization
import CP15.OddCycleLocal

namespace CP15

/-- The necessary five-radius angle cost for alternating occupied gaps.
The next index is the cyclic successor in `Fin 5`. -/
noncomputable def localAngularCost (b α : ℝ) (r : Fin 5 → ℝ) : ℝ :=
  ∑ i, max (α + contactAngle b (r i) + contactAngle b (r (i + 1)))
    (contactAngle (r (i + 1)) (r i))

private theorem max_margin_of_two_linearizations (g d σ x e : ℝ)
    (he : 0 ≤ e)
    (hg : |g - σ - (81 / 100 : ℝ) * x| ≤ (2 / 100 : ℝ) * e)
    (hd : |d - σ + (43 / 100 : ℝ) * x| ≤ (1 / 100 : ℝ) * e) :
    (43 / 100 : ℝ) * |x| - (2 / 100 : ℝ) * e ≤ max g d - σ := by
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
The direct maximum estimate loses only `0.04`, yielding `0.132 = 33/250`. -/
theorem local_angular_stability (b α r₀ : ℝ) (r : Fin 5 → ℝ)
    (hblo : (35213 / 10000 : ℝ) ≤ b) (hbhi : b ≤ 35214 / 10000)
    (h₀ : r₀ ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hr : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hbalance : α + 2 * contactAngle b r₀ = contactAngle r₀ r₀) :
    (33 / 250 : ℝ) * (∑ i, |r i - r₀|) ≤
      localAngularCost b α r - 5 * (α + 2 * contactAngle b r₀) := by
  let t : Fin 5 → ℝ := fun i => r i - r₀
  let σ : ℝ := α + 2 * contactAngle b r₀
  have hpoint (i : Fin 5) :
      (43 / 100 : ℝ) * |fiveAdjacentSum t i| -
        (2 / 100 : ℝ) * fiveAdjacentSum (fun j => |t j|) i ≤
      max (α + contactAngle b (r i) + contactAngle b (r (i + 1)))
        (contactAngle (r (i + 1)) (r i)) - σ := by
    apply max_margin_of_two_linearizations
    · dsimp [fiveAdjacentSum]
      positivity
    · have h1 := local_outer_angle_linearization b (r i) r₀ hblo hbhi (hr i) h₀
      have h2 := local_outer_angle_linearization b (r (i + 1)) r₀
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
    · have hpair := local_pair_angle_linearization (r i) (r (i + 1)) r₀
        (hr i) (hr (i + 1)) h₀
      dsimp [σ, fiveAdjacentSum, t]
      rw [hbalance]
      exact hpair
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hsum :
      (43 / 100 : ℝ) * (∑ i, |fiveAdjacentSum t i|) -
        (2 / 100 : ℝ) * (∑ i, fiveAdjacentSum (fun j => |t j|) i) ≤
      localAngularCost b α r - 5 * σ := by
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
      localAngularCost] using hs
  rw [five_adjacent_sum_total] at hsum
  have hodd := five_adjacent_sum_l1_lower t
  dsimp [t, σ] at hsum hodd
  linarith

/-- The coefficient stated in the paper follows from the stronger checked
maximum estimate, with no derivative or linearization premise left over. -/
theorem local_angular_stability_paper_margin (b α r₀ : ℝ) (r : Fin 5 → ℝ)
    (hblo : (35213 / 10000 : ℝ) ≤ b) (hbhi : b ≤ 35214 / 10000)
    (h₀ : r₀ ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hr : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hbalance : α + 2 * contactAngle b r₀ = contactAngle r₀ r₀) :
    (9 / 125 : ℝ) * (∑ i, |r i - r₀|) ≤
      localAngularCost b α r - 5 * (α + 2 * contactAngle b r₀) := by
  have h := local_angular_stability b α r₀ r hblo hbhi h₀ hr hbalance
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (r i - r₀))
  linarith

theorem local_angular_cost_unique_reference (b α r₀ : ℝ) (r : Fin 5 → ℝ)
    (hblo : (35213 / 10000 : ℝ) ≤ b) (hbhi : b ≤ 35214 / 10000)
    (h₀ : r₀ ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hr : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hbalance : α + 2 * contactAngle b r₀ = contactAngle r₀ r₀)
    (hcost : localAngularCost b α r ≤ 5 * (α + 2 * contactAngle b r₀)) :
    ∀ i, r i = r₀ := by
  have hmargin := local_angular_stability_paper_margin b α r₀ r hblo hbhi h₀ hr hbalance
  have hz := zero_vector_of_local_margin (fun i => r i - r₀) _ hmargin
    (sub_nonpos.mpr hcost)
  intro i
  exact sub_eq_zero.mp (hz i)

theorem five_successor_sum (a : Fin 5 → ℝ) : (∑ i, a (i + 1)) = ∑ i, a i := by
  simp [Fin.sum_univ_five]
  ring

/-- The alternating-gap necessary inequality is obtained by summing
actual endpoint clearances and consecutive inner clearances. No equality
or double outer contact is assumed for an arbitrary inner center. -/
theorem angular_cost_le_turn_of_alternating_gaps
    (b α turn : ℝ) (r a c e : Fin 5 → ℝ)
    (ha : ∀ i, contactAngle b (r i) ≤ a i)
    (hc : ∀ i, contactAngle b (r i) ≤ c i)
    (he : ∀ i, α ≤ e i)
    (hp : ∀ i, contactAngle (r (i + 1)) (r i) ≤ c i + e i + a (i + 1))
    (hturn : (∑ i, (a i + c i + e i)) = turn) :
    localAngularCost b α r ≤ turn := by
  have hpoint (i : Fin 5) :
      max (α + contactAngle b (r i) + contactAngle b (r (i + 1)))
        (contactAngle (r (i + 1)) (r i)) ≤ c i + e i + a (i + 1) := by
    apply max_le
    · linarith [hc i, he i, ha (i + 1)]
    · exact hp i
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  change localAngularCost b α r ≤ _ at hs
  simp only [Finset.sum_add_distrib, five_successor_sum] at hs hturn
  linarith

end CP15
