import CP15.ExpandedLocalStability
import CP15.LocalAlternatingClosed

namespace CP15

set_option maxHeartbeats 0

/-- A wider independently checked local cube. Its smaller positive margin
allows the global cover to stop earlier while retaining a full proof. -/
theorem candidate_expanded_angular_stability (r : Fin 5 → ℝ)
    (hr : ∀ i, r i ∈ Set.Icc (42 / 25 : ℝ) (43 / 25)) :
    (3 / 250 : ℝ) * (∑ i, |r i - candidateInnerRadius|) ≤
      localAngularCost candidateB (outerAlpha candidateB) r - 2 * Real.pi := by
  have h := expanded_angular_stability candidateB (outerAlpha candidateB)
    candidateInnerRadius r candidateB_local_bounds.1.le candidateB_local_bounds.2.le
    (show candidateInnerRadius ∈ Set.Icc (42 / 25 : ℝ) (43 / 25) by
      constructor <;> linarith [candidateInnerRadius_local_bounds.1,
        candidateInnerRadius_local_bounds.2]) hr candidate_angle_reference_balance
  rw [candidate_outer_inner_angle_balance] at h
  convert h using 1 <;> ring

/-- The expanded closed cube contains only the candidate radii whenever
the actual necessary alternating angular budget holds below the candidate. -/
theorem expanded_local_angle_budget_closed (b : ℝ) (r : Fin 5 → ℝ)
    (hb : 3 < b) (hbB : b ≤ candidateB)
    (hr : ∀ i, r i ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hcost : localAngularCost b (outerAlpha b) r ≤ 2 * Real.pi) :
    b = candidateB ∧ ∀ i, r i = candidateInnerRadius := by
  have hcostB : localAngularCost candidateB (outerAlpha candidateB) r ≤ 2 * Real.pi := by
    apply le_trans (b := localAngularCost b (outerAlpha b) r) _ hcost
    apply Finset.sum_le_sum
    intro i _
    apply max_le_max
    · have hα := outerAlpha_antitone_radius b candidateB (by linarith) hbB
      have hγ := contactAngle_antitone_outer_radius b candidateB (r i) hb hbB
        (by linarith [(hr i).1]) (by linarith [(hr i).2])
      have hγn := contactAngle_antitone_outer_radius b candidateB (r (i + 1)) hb hbB
        (by linarith [(hr (i + 1)).1]) (by linarith [(hr (i + 1)).2])
      linarith
    · exact le_rfl
  have hmargin := candidate_expanded_angular_stability r hr
  have hn := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => abs_nonneg (r i - candidateInnerRadius))
  have hsum : (∑ i, |r i - candidateInnerRadius|) = 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      abs_nonneg (r i - candidateInnerRadius))).1 hsum
  have hrad (i : Fin 5) : r i = candidateInnerRadius := by
    have hi := abs_eq_zero.mp (hz i (Finset.mem_univ i))
    exact sub_eq_zero.mp hi
  have hsmall : ∀ i, r i ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500) := by
    intro i
    rw [hrad i]
    exact ⟨candidateInnerRadius_local_bounds.1.le, candidateInnerRadius_local_bounds.2.le⟩
  exact local_alternating_angle_budget_closed b r hb hbB hsmall hcost

end CP15
