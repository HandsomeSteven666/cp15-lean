import CP15.AlternatingGeometry
import CP15.ActualOuterCycle

namespace CP15

/-- Once a labelled configuration is known to have the local alternating
order and radii, the exact gap equalities determine all coordinates up to a
centered orthogonal transformation and relabeling. -/
theorem local_alternating_pattern_congruent
    (q : Fin 15 → Plane)
    (hmono : StrictMono (fun i => polarArg (q i)))
    (hsep : Separated q 2)
    (hleft : ∀ i, ‖q (alternatingLeft i)‖ ∈ Set.Icc (17 / 5 : ℝ) candidateB)
    (hright : ∀ i, ‖q (alternatingRight i)‖ ∈ Set.Icc (17 / 5 : ℝ) candidateB)
    (hr : ∀ i, ‖q (alternatingInner i)‖ ∈
      Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    CenteredCongruent15 q Candidate.pointAtSeparationTwo := by
  let θ : Fin 15 → ℝ := fun i => polarArg (q i)
  have hframe : LiftedFifteenFrame q θ := literal_fifteen_frame q hmono
  have hrigid := local_alternating_variable_outer_rigidity
    q θ hframe hsep hleft hright hr
  rcases hrigid with ⟨hinner, hleftB, hrightB, hleftGap, hrightGap, houterGap⟩
  let ix : Fin 5 → Fin 15 := alternatingInner
  let o : Fin 10 → Fin 15 := alternatingOuter
  let u : Fin 5 → Fin 10 := alternatingOuterPosition
  let φ : Fin 5 → ℝ := fun i => θ (ix i)
  let ψ : Fin 10 → ℝ := fun k => θ (o k)
  have hgap (i : Fin 5) : cyclicAngleGap φ i = 2 * Real.pi / 5 := by
    rw [show cyclicAngleGap φ i =
      cyclicAngleGap (fun j : Fin 5 => θ (alternatingInner j)) i by
        simp [φ, ix]]
    rw [cyclic_inner_gap_eq_forwardArc]
    rw [alternating_inner_forward_arc_decomposition]
    rw [hrightGap i, houterGap i, hleftGap (i + 1)]
    nlinarith [candidate_outer_inner_angle_balance]
  have hlift (i : Fin 5) :
      φ i = polarArg (q (ix i)) ∨
        φ i = polarArg (q (ix i)) + 2 * Real.pi := by
    exact Or.inl (by rfl)
  obtain ⟨a, hrotation⟩ :=
    exists_rotation_matching_inner_pentagon q ix φ hinner hlift hgap
  have hphase (i : Fin 5) :
      φ i = ψ (u i) + contactAngle candidateB candidateInnerRadius := by
    have hlt : alternatingLeft i < alternatingInner i :=
      Fin.lt_iff_val_lt_val.mpr (by simp [alternatingLeft, alternatingInner])
    have hgap' := hleftGap i
    rw [show forwardArc15 θ (alternatingLeft i) (alternatingInner i) =
      θ (alternatingInner i) - θ (alternatingLeft i) by
        simp [forwardArc15, hlt]] at hgap'
    change θ (alternatingInner i) =
      θ (alternatingOuter (alternatingOuterPosition i)) +
        contactAngle candidateB candidateInnerRadius
    rw [alternatingOuterPosition_left]
    linarith
  have houterGap' (i : Fin 5) : cyclicAngleGap ψ (u i) =
      2 * contactAngle candidateB candidateInnerRadius := by
    rw [show cyclicAngleGap ψ (u i) =
      cyclicAngleGap (fun k : Fin 10 => θ (alternatingOuter k))
        (alternatingOuterPosition i) by simp [ψ, u, o]]
    rw [cyclic_outer_gap_eq_forwardArc]
    have hsplit : forwardArc15 θ (alternatingLeft i) (alternatingRight i) =
        forwardArc15 θ (alternatingLeft i) (alternatingInner i) +
          forwardArc15 θ (alternatingInner i) (alternatingRight i) := by
      have h₁ : alternatingLeft i < alternatingInner i :=
        Fin.lt_iff_val_lt_val.mpr (by simp [alternatingLeft, alternatingInner])
      have h₂ : alternatingInner i < alternatingRight i :=
        Fin.lt_iff_val_lt_val.mpr (by simp [alternatingInner, alternatingRight])
      have h₃ : alternatingLeft i < alternatingRight i :=
        Fin.lt_iff_val_lt_val.mpr (by simp [alternatingLeft, alternatingRight])
      simp [forwardArc15, h₁, h₂, h₃]
    rw [hsplit, hleftGap i, hrightGap i]
    ring
  have harg (k : Fin 10) : polarArg (q (o k)) = ψ k := by rfl
  have hR (k : Fin 10) : ‖q (o k)‖ = candidateB := by
    fin_cases k <;> norm_num [o, alternatingOuter] <;>
      first
      | exact hleftB 0
      | exact hrightB 0
      | exact hleftB 1
      | exact hrightB 1
      | exact hleftB 2
      | exact hrightB 2
      | exact hleftB 3
      | exact hrightB 3
      | exact hleftB 4
      | exact hrightB 4
  have houterRotation := actual_contact_pairs_match_candidate
    q ix o u φ ψ a hinner hR harg hlift hphase houterGap' hrotation
  let indices := actualAllIndex ix o u
  have hindices : Function.Bijective indices := by
    decide
  let actualEquiv : (Fin 5 ⊕ (Fin 5 ⊕ Fin 5)) ≃ Fin 15 :=
    Equiv.ofBijective indices hindices
  let σ : Fin 15 ≃ Fin 15 := actualEquiv.symm.trans candidateAllEquiv
  have hpoint (l : Fin 5 ⊕ (Fin 5 ⊕ Fin 5)) :
      q (indices l) = planeRotation a
        (Candidate.pointAtSeparationTwo (candidateAllIndex l)) := by
    apply planeComplex_injective
    cases l with
    | inl i =>
      simpa [indices, actualAllIndex, candidateAllIndex,
        _root_.rotation_apply, planeComplex_planeRotation] using (hrotation i).symm
    | inr lr =>
      cases lr with
      | inl i =>
        simpa [indices, actualAllIndex, candidateAllIndex,
          _root_.rotation_apply, planeComplex_planeRotation] using
          (houterRotation i).1.symm
      | inr i =>
        simpa [indices, actualAllIndex, candidateAllIndex,
          _root_.rotation_apply, planeComplex_planeRotation] using
          (houterRotation i).2.symm
  refine ⟨σ, planeRotation a, ?_⟩
  intro j
  let l := actualEquiv.symm j
  have hidx : indices l = j := actualEquiv.apply_symm_apply j
  calc
    q j = q (indices l) := by rw [hidx]
    _ = planeRotation a
        (Candidate.pointAtSeparationTwo (candidateAllIndex l)) := hpoint l
    _ = planeRotation a
        (Candidate.pointAtSeparationTwo (σ j)) := by
          simp [σ, l, candidateAllEquiv]

end CP15
