import CP15.CandidateAngles
import CP15.LocalAngularStability

namespace CP15

theorem contactCos_strict_mono_outer_radius (b B r : ℝ)
    (hb : 3 < b) (hbB : b < B) (hr : 0 < r) (hru : r ≤ 12 / 5) :
    contactCos b r < contactCos B r := by
  have hB : 3 < B := by linarith
  have hpositive : 0 < (B - 3) * (b - 3) := mul_pos (by linarith) (by linarith)
  have hprod : 9 < B * b := by nlinarith
  have hrsq : r ^ 2 ≤ (12 / 5 : ℝ) ^ 2 := by nlinarith
  have hfactor : 0 < (B - b) * (B * b - r ^ 2 + 4) :=
    mul_pos (by linarith) (by nlinarith)
  have hscaled := mul_pos (show 0 < 2 * r by positivity) hfactor
  unfold contactCos
  apply (div_lt_div_iff₀ (by positivity : 0 < 2 * b * r)
    (by positivity : 0 < 2 * B * r)).2
  nlinarith

theorem contactAngle_antitone_outer_radius (b B r : ℝ)
    (hb : 3 < b) (hbB : b ≤ B) (hr : 0 < r) (hru : r ≤ 12 / 5) :
    contactAngle B r ≤ contactAngle b r := by
  rcases eq_or_lt_of_le hbB with heq | hlt
  · rw [heq]
  · exact Real.arccos_le_arccos (contactCos_strict_mono_outer_radius b B r hb hlt hr hru).le

theorem local_contactAngle_strict_radius_comparison (b r : ℝ)
    (hb : 3 < b) (hbB : b < candidateB)
    (hr : r ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    contactAngle candidateB r < contactAngle b r := by
  have hr0 : 0 < r := by linarith [hr.1]
  have hcos := contactCos_strict_mono_outer_radius b candidateB r hb hbB hr0 (by linarith [hr.2])
  have hbcos : -1 ≤ contactCos b r := by
    have hn : 0 < b ^ 2 + r ^ 2 - 4 := by nlinarith [sq_nonneg r]
    have hc : 0 < contactCos b r := div_pos hn (by positivity)
    linarith
  have hbox := local_outer_derivative_bounds candidateB r
    candidateB_local_bounds.1.le candidateB_local_bounds.2.le hr.1 hr.2
  have hcsq := contactCos_sq_lt_one candidateB r candidateB_pos hr0 hbox.1
  exact Real.arccos_lt_arccos hbcos hcos (by nlinarith)

theorem outerAlpha_antitone_radius (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B) :
    outerAlpha B ≤ outerAlpha b := by
  have hB : 0 < B := hb.trans_le hbB
  have hrec : 1 / B ≤ 1 / b := (div_le_div_iff₀ hB hb).2 (by linarith)
  exact mul_le_mul_of_nonneg_left (Real.arcsin_le_arcsin hrec) (by norm_num)

theorem outerAlpha_strict_radius_comparison (b B : ℝ) (hb : 1 < b) (hbB : b < B) :
    outerAlpha B < outerAlpha b := by
  have hb0 : 0 < b := by linarith
  have hB0 : 0 < B := by linarith
  have hrec : 1 / B < 1 / b := (div_lt_div_iff₀ hB0 hb0).2 (by linarith)
  have hrecLo : -1 ≤ 1 / B := by
    have hrec0 : 0 ≤ 1 / B := by positivity
    linarith
  have hrecHi : 1 / b ≤ 1 := (div_le_one hb0).2 (by linarith)
  exact mul_lt_mul_of_pos_left (Real.arcsin_lt_arcsin hrecLo hrec hrecHi) (by norm_num)

theorem local_angular_cost_antitone_radius (b B : ℝ) (r : Fin 5 → ℝ)
    (hb : 3 < b) (hbB : b ≤ B)
    (hr : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    localAngularCost B (outerAlpha B) r ≤ localAngularCost b (outerAlpha b) r := by
  apply Finset.sum_le_sum
  intro i _
  apply max_le_max
  · have hα := outerAlpha_antitone_radius b B (by linarith) hbB
    have hγ := contactAngle_antitone_outer_radius b B (r i) hb hbB
      (by linarith [(hr i).1]) (by linarith [(hr i).2])
    have hγnext := contactAngle_antitone_outer_radius b B (r (i + 1)) hb hbB
      (by linarith [(hr (i + 1)).1]) (by linarith [(hr (i + 1)).2])
    linarith
  · exact le_rfl

/-- The local analytic inequality specialized to the exact candidate:
all derivative, reference-radius, and angle-balance hypotheses have been
proved internally, so only membership in the local cube is required. -/
theorem candidate_local_angular_stability (r : Fin 5 → ℝ)
    (hr : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    (33 / 250 : ℝ) * (∑ i, |r i - candidateInnerRadius|) ≤
      localAngularCost candidateB (outerAlpha candidateB) r - 2 * Real.pi := by
  have h := local_angular_stability candidateB (outerAlpha candidateB) candidateInnerRadius r
    candidateB_local_bounds.1.le candidateB_local_bounds.2.le
    ⟨candidateInnerRadius_local_bounds.1.le, candidateInnerRadius_local_bounds.2.le⟩
    hr candidate_angle_reference_balance
  rw [candidate_outer_inner_angle_balance] at h
  convert h using 1 <;> ring

/-- The whole local alternating analytic closure. Any radius below the
candidate violates the necessary angle budget. At the candidate radius,
that budget forces every inner radius to be the exact regular-pentagon
radius. The geometric derivation of the budget is a separate theorem. -/
theorem local_alternating_angle_budget_closed (b : ℝ) (r : Fin 5 → ℝ)
    (hb : 3 < b) (hbB : b ≤ candidateB)
    (hr : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hcost : localAngularCost b (outerAlpha b) r ≤ 2 * Real.pi) :
    b = candidateB ∧ ∀ i, r i = candidateInnerRadius := by
  have hcostB := (local_angular_cost_antitone_radius b candidateB r hb hbB hr).trans hcost
  have hreference : localAngularCost candidateB (outerAlpha candidateB) r ≤
      5 * (outerAlpha candidateB + 2 * contactAngle candidateB candidateInnerRadius) := by
    rw [candidate_outer_inner_angle_balance]
    nlinarith
  have hrad := local_angular_cost_unique_reference candidateB (outerAlpha candidateB)
    candidateInnerRadius r candidateB_local_bounds.1.le candidateB_local_bounds.2.le
    ⟨candidateInnerRadius_local_bounds.1.le, candidateInnerRadius_local_bounds.2.le⟩
    hr candidate_angle_reference_balance hreference
  refine ⟨?_, hrad⟩
  by_contra hneq
  have hlt : b < candidateB := lt_of_le_of_ne hbB hneq
  have hα := outerAlpha_strict_radius_comparison b candidateB (by linarith) hlt
  have hγ := contactAngle_antitone_outer_radius b candidateB candidateInnerRadius hb hbB
    candidateInnerRadius_pos (by linarith [candidateInnerRadius_local_bounds.2])
  have hfirst : 2 * Real.pi / 5 < outerAlpha b + 2 * contactAngle b candidateInnerRadius := by
    linarith [candidate_outer_inner_angle_balance]
  have hpoint (i : Fin 5) : 2 * Real.pi / 5 <
      max (outerAlpha b + contactAngle b (r i) + contactAngle b (r (i + 1)))
        (contactAngle (r (i + 1)) (r i)) := by
    rw [hrad i, hrad (i + 1)]
    exact (by linarith : 2 * Real.pi / 5 < outerAlpha b +
      contactAngle b candidateInnerRadius + contactAngle b candidateInnerRadius).trans_le
        (le_max_left _ _)
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => (hpoint i).le)
    ⟨0, Finset.mem_univ 0, hpoint 0⟩
  change (∑ _ : Fin 5, 2 * Real.pi / 5) < localAngularCost b (outerAlpha b) r at hsum
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hsum
  linarith

/-- At equality, every nonnegative endpoint and empty-gap slack vanishes.
This is the angle-level rigidity consequence, without an assumption that
an arbitrary inner center initially touches both gap endpoints. -/
theorem local_alternating_gaps_closed (b : ℝ) (r a c e : Fin 5 → ℝ)
    (hb : 3 < b) (hbB : b ≤ candidateB)
    (hr : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (ha : ∀ i, contactAngle b (r i) ≤ a i)
    (hc : ∀ i, contactAngle b (r i) ≤ c i)
    (he : ∀ i, outerAlpha b ≤ e i)
    (hp : ∀ i, contactAngle (r (i + 1)) (r i) ≤ c i + e i + a (i + 1))
    (hturn : (∑ i, (a i + c i + e i)) = 2 * Real.pi) :
    b = candidateB ∧ (∀ i, r i = candidateInnerRadius) ∧
      (∀ i, a i = contactAngle candidateB candidateInnerRadius) ∧
      (∀ i, c i = contactAngle candidateB candidateInnerRadius) ∧
      (∀ i, e i = outerAlpha candidateB) := by
  have hcost := angular_cost_le_turn_of_alternating_gaps b (outerAlpha b)
    (2 * Real.pi) r a c e ha hc he hp hturn
  obtain ⟨hbEq, hrEq⟩ := local_alternating_angle_budget_closed b r hb hbB hr hcost
  subst b
  have ha' (i : Fin 5) : contactAngle candidateB candidateInnerRadius ≤ a i := by
    simpa only [hrEq i] using ha i
  have hc' (i : Fin 5) : contactAngle candidateB candidateInnerRadius ≤ c i := by
    simpa only [hrEq i] using hc i
  let w : Fin 5 → ℝ := fun i => (a i - contactAngle candidateB candidateInnerRadius) +
    (c i - contactAngle candidateB candidateInnerRadius) + (e i - outerAlpha candidateB)
  have hw0 (i : Fin 5) : 0 ≤ w i := by dsimp [w]; linarith [ha' i, hc' i, he i]
  have hwSum : (∑ i, w i) = 0 := by
    have hpoint (i : Fin 5) : w i = a i + c i + e i - 2 * Real.pi / 5 := by
      dsimp [w]
      linarith [candidate_outer_inner_angle_balance]
    simp only [hpoint, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, hturn]
    ring
  have hwEq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => hw0 i)).1 hwSum
  have hz (i : Fin 5) := hwEq i (Finset.mem_univ i)
  refine ⟨rfl, hrEq, ?_, ?_, ?_⟩
  all_goals intro i; have h := hz i; dsimp [w] at h; linarith [ha' i, hc' i, he i]

end CP15
