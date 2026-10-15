import CP15.AlternatingCoordinates

open Filter Topology

namespace CP15

private theorem planeComplex_as_coordinate_sum (x : Plane) :
    planeComplex x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [planeComplex]

private theorem eventually_norm_gt_at
    (r : Fin 15 → Plane) (i : Fin 15) (c : ℝ)
    (h : c < ‖r i‖) : ∀ᶠ q : Fin 15 → Plane in 𝓝 r, c < ‖q i‖ := by
  have hc : ContinuousAt (fun q : Fin 15 → Plane => ‖q i‖) r := by
    exact ((continuous_apply i).norm).continuousAt
  exact hc.tendsto.eventually (eventually_gt_nhds h)

private theorem eventually_norm_lt_at
    (r : Fin 15 → Plane) (i : Fin 15) (c : ℝ)
    (h : ‖r i‖ < c) : ∀ᶠ q : Fin 15 → Plane in 𝓝 r, ‖q i‖ < c := by
  have hc : ContinuousAt (fun q : Fin 15 → Plane => ‖q i‖) r := by
    exact ((continuous_apply i).norm).continuousAt
  exact hc.tendsto.eventually (eventually_lt_nhds h)

/-- Strict polar order is stable under small perturbations when no reference
point lies on the branch cut of the principal argument. -/
theorem eventually_strictPolarArg
    (r : Fin 15 → Plane)
    (hmono : StrictMono (fun i => polarArg (r i)))
    (hcut : ∀ i, planeComplex (r i) ∈ Complex.slitPlane) :
    ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      StrictMono (fun i => polarArg (q i)) := by
  have harg (i : Fin 15) :
      ContinuousAt (fun q : Fin 15 → Plane => polarArg (q i)) r := by
    have hpc : ContinuousAt planeComplex (r i) := by
      have heq : planeComplex =
          fun x : Plane => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
        funext x
        exact planeComplex_as_coordinate_sum x
      rw [heq]
      fun_prop
    have hpolar : ContinuousAt (fun x : Plane => polarArg x) (r i) := by
      unfold polarArg
      exact (Complex.continuousAt_arg (hcut i)).comp hpc
    have heval : ContinuousAt (fun q : Fin 15 → Plane => q i) r := by
      exact (continuous_apply i).continuousAt
    exact ContinuousAt.comp'
      (f := fun q : Fin 15 → Plane => q i)
      (g := fun x : Plane => polarArg x) (x := r) hpolar heval
  have hpair : ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      ∀ i j : Fin 15, i < j → polarArg (q i) < polarArg (q j) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i < j
    · have hgap : 0 < polarArg (r j) - polarArg (r i) :=
        sub_pos.mpr (hmono hij)
      have ht : Tendsto
          (fun q : Fin 15 → Plane => polarArg (q j) - polarArg (q i))
          (𝓝 r) (𝓝 (polarArg (r j) - polarArg (r i))) :=
        (harg j).tendsto.sub (harg i).tendsto
      filter_upwards [ht.eventually (eventually_gt_nhds hgap)] with q hq
      intro _
      exact sub_pos.mp hq
    · exact Filter.Eventually.of_forall fun q hi => False.elim (hij hi)
  filter_upwards [hpair] with q hq
  change ∀ i j : Fin 15, i < j → polarArg (q i) < polarArg (q j)
  exact hq

/-- All hypotheses of the local alternating rigidity theorem persist in a
neighborhood of a strictly ordered reference packing, apart from the outer
upper radius bound, which follows from feasibility in the candidate disk. -/
theorem eventually_localAlternatingHypotheses
    (r : Fin 15 → Plane)
    (hmono : StrictMono (fun i => polarArg (r i)))
    (hcut : ∀ i, planeComplex (r i) ∈ Complex.slitPlane)
    (hleft : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingLeft i)‖)
    (hright : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingRight i)‖)
    (hinnerLo : ∀ i, (1697 / 1000 : ℝ) < ‖r (alternatingInner i)‖)
    (hinnerHi : ∀ i, ‖r (alternatingInner i)‖ < (853 / 500 : ℝ)) :
    ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      StrictMono (fun i => polarArg (q i)) ∧
      (∀ i, (17 / 5 : ℝ) < ‖q (alternatingLeft i)‖) ∧
      (∀ i, (17 / 5 : ℝ) < ‖q (alternatingRight i)‖) ∧
      (∀ i, (1697 / 1000 : ℝ) < ‖q (alternatingInner i)‖) ∧
      (∀ i, ‖q (alternatingInner i)‖ < (853 / 500 : ℝ)) := by
  have horder := eventually_strictPolarArg r hmono hcut
  have hleftEvent : ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      ∀ i, (17 / 5 : ℝ) < ‖q (alternatingLeft i)‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_norm_gt_at r (alternatingLeft i) (17 / 5) (hleft i)
  have hrightEvent : ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      ∀ i, (17 / 5 : ℝ) < ‖q (alternatingRight i)‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_norm_gt_at r (alternatingRight i) (17 / 5) (hright i)
  have hinnerLoEvent : ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      ∀ i, (1697 / 1000 : ℝ) < ‖q (alternatingInner i)‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_norm_gt_at r (alternatingInner i) (1697 / 1000)
      (hinnerLo i)
  have hinnerHiEvent : ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      ∀ i, ‖q (alternatingInner i)‖ < (853 / 500 : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_norm_lt_at r (alternatingInner i) (853 / 500)
      (hinnerHi i)
  filter_upwards [horder, hleftEvent, hrightEvent,
    hinnerLoEvent, hinnerHiEvent] with q hqorder hqleft hqright hqinnerLo hqinnerHi
  exact ⟨hqorder, hqleft, hqright, hqinnerLo, hqinnerHi⟩

/-- Near a feasible, strictly ordered alternating reference with the stated
strict radial margins, every feasible packing is congruent to the candidate.
This gives a genuine local isolation statement in the feasible set. -/
theorem eventually_feasible_congruent_of_localAlternatingReference
    (r : Fin 15 → Plane)
    (hmono : StrictMono (fun i => polarArg (r i)))
    (hcut : ∀ i, planeComplex (r i) ∈ Complex.slitPlane)
    (hleft : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingLeft i)‖)
    (hright : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingRight i)‖)
    (hinnerLo : ∀ i, (1697 / 1000 : ℝ) < ‖r (alternatingInner i)‖)
    (hinnerHi : ∀ i, ‖r (alternatingInner i)‖ < (853 / 500 : ℝ)) :
    ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
      q ∈ FeasibleSet15 candidateB →
        CenteredCongruent15 q Candidate.pointAtSeparationTwo := by
  have hnear := eventually_localAlternatingHypotheses r hmono hcut
    hleft hright hinnerLo hinnerHi
  filter_upwards [hnear] with q hq hqFeasible
  rcases hqFeasible with ⟨hdisk, hsep⟩
  apply local_alternating_pattern_congruent q hq.1 hsep
  · intro i
    exact ⟨by linarith [hq.2.1 i], hdisk (alternatingLeft i)⟩
  · intro i
    exact ⟨by linarith [hq.2.2.1 i], hdisk (alternatingRight i)⟩
  · intro i
    exact ⟨by linarith [hq.2.2.2.1 i], by linarith [hq.2.2.2.2 i]⟩

/-- A feasible alternating reference is itself the candidate up to
congruence, and it is isolated from other feasible congruence classes. -/
theorem localAlternatingReference_congruent_and_isolated
    (r : Fin 15 → Plane)
    (hr : r ∈ FeasibleSet15 candidateB)
    (hmono : StrictMono (fun i => polarArg (r i)))
    (hcut : ∀ i, planeComplex (r i) ∈ Complex.slitPlane)
    (hleft : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingLeft i)‖)
    (hright : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingRight i)‖)
    (hinnerLo : ∀ i, (1697 / 1000 : ℝ) < ‖r (alternatingInner i)‖)
    (hinnerHi : ∀ i, ‖r (alternatingInner i)‖ < (853 / 500 : ℝ)) :
    CenteredCongruent15 r Candidate.pointAtSeparationTwo ∧
      ∀ᶠ q : Fin 15 → Plane in 𝓝 r,
        q ∈ FeasibleSet15 candidateB →
          CenteredCongruent15 q Candidate.pointAtSeparationTwo := by
  have hcongruent : CenteredCongruent15 r Candidate.pointAtSeparationTwo :=
    local_alternating_pattern_congruent r hmono hr.2
      (fun i => ⟨le_of_lt (hleft i), hr.1 (alternatingLeft i)⟩)
      (fun i => ⟨le_of_lt (hright i), hr.1 (alternatingRight i)⟩)
      (fun i => ⟨le_of_lt (hinnerLo i), le_of_lt (hinnerHi i)⟩)
  refine ⟨hcongruent, ?_⟩
  exact eventually_feasible_congruent_of_localAlternatingReference
    r hmono hcut hleft hright hinnerLo hinnerHi

end CP15
