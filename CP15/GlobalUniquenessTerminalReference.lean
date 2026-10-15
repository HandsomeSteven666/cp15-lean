import CP15.GlobalUniquenessLocalReference

namespace CP15

/-- A terminal equality pattern yields an actual feasible reference in the
strictly ordered local rigidity region. The reindexing matches each inner
point with its two adjacent outer contacts; a final rotation centers the
empty angular gap at the principal branch cut. -/
theorem exists_localAlternatingReference_of_terminalData
    (q : Fin 15 → Plane) (ix : Fin 5 → Fin 15)
    (o : Fin 10 → Fin 15) (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ)
    (hix : Function.Injective ix) (ho : Function.Injective o)
    (hparity : ∃ a : Fin 2, ∀ i, (u i).val = a.val + 2 * i.val)
    (hinner : ∀ i, ‖q (ix i)‖ = candidateInnerRadius)
    (houterRadius : ∀ k, ‖q (o k)‖ = candidateB)
    (houterComplete : ∀ j, ‖q j‖ = candidateB → ∃ k, o k = j)
    (hinnerComplete : ∀ j, ‖q j‖ < candidateB → ∃ i, ix i = j)
    (hlift : ∀ i, φ i = polarArg (q (ix i)) ∨
      φ i = polarArg (q (ix i)) + 2 * Real.pi)
    (hempty : ∀ k, (∀ i, u i ≠ k) →
      cyclicAngleGap (fun j => polarArg (q (o j))) k = outerAlpha candidateB)
    (hoccupied : ∀ i,
      cyclicAngleGap (fun j => polarArg (q (o j))) (u i) =
        2 * contactAngle candidateB candidateInnerRadius)
    (hphase : ∀ i, φ i = polarArg (q (o (u i))) +
      contactAngle candidateB candidateInnerRadius)
    (hq : q ∈ FeasibleSet15 candidateB) :
    ∃ r, r ∈ FeasibleSet15 candidateB ∧
      StrictMono (fun i => polarArg (r i)) ∧
      (∀ i, planeComplex (r i) ∈ Complex.slitPlane) ∧
      (∀ i, (17 / 5 : ℝ) < ‖r (alternatingLeft i)‖) ∧
      (∀ i, (17 / 5 : ℝ) < ‖r (alternatingRight i)‖) ∧
      (∀ i, (1697 / 1000 : ℝ) < ‖r (alternatingInner i)‖) ∧
      (∀ i, ‖r (alternatingInner i)‖ < (853 / 500 : ℝ)) := by
  let ψ : Fin 10 → ℝ := fun k => polarArg (q (o k))
  let θ : Fin 15 → ℝ := terminalAlternatingLift ψ u φ
  have hψmono : StrictMono ψ := by
    exact terminalOuterAngle_strictMono ψ u hparity
      (by simpa [ψ] using hempty) (by simpa [ψ] using hoccupied)
  have hwrap : ψ 9 < ψ 0 + 2 * Real.pi := by
    have h := Complex.arg_lt_arg_add_two_pi
      (planeComplex (q (o 9))) (planeComplex (q (o 0)))
    simpa [ψ, polarArg] using h
  have hθmono : StrictMono θ := by
    exact terminalAlternatingLift_strictMono ψ u φ hparity
      (by simpa [ψ] using hphase)
      (by simpa [ψ] using hempty) (by simpa [ψ] using hoccupied)
  have hθspan : θ 14 - θ 0 < 2 * Real.pi :=
    terminalAlternatingLift_span_lt_twoPi ψ u φ hparity hψmono hwrap
  have hactual : Function.Bijective (actualAllIndex ix o u) :=
    actualAllIndex_bijective q ix o u hparity hix ho hinner houterRadius
      houterComplete hinnerComplete hq
  let qAlt := actualAlternatingConfig q ix o u
  have hqAltCong : CenteredCongruent15 qAlt q :=
    actualAlternatingConfig_congruent q ix o u hactual
  have hqAlt : qAlt ∈ FeasibleSet15 candidateB :=
    feasible_of_centeredCongruent15 qAlt q candidateB hqAltCong hq
  have hqleft (i : Fin 5) : qAlt (alternatingLeft i) = q (o (u i)) := by
    simp [qAlt, actualAlternatingConfig, actualAlternatingIndex_left]
  have hqinner (i : Fin 5) : qAlt (alternatingInner i) = q (ix i) := by
    simp [qAlt, actualAlternatingConfig, actualAlternatingIndex_inner]
  have hqright (i : Fin 5) : qAlt (alternatingRight i) = q (o (u i + 1)) := by
    simp [qAlt, actualAlternatingConfig, actualAlternatingIndex_right]
  have hnonzero : ∀ i, qAlt i ≠ 0 := by
    intro j
    rcases alternating_position_complete j with ⟨i, hj⟩ | ⟨i, hj⟩ | ⟨i, hj⟩
    · subst j
      rw [hqleft]
      intro hz
      have hb := houterRadius (u i)
      rw [hz] at hb
      have hb0 : (0 : ℝ) = candidateB := by simpa using hb
      exact (ne_of_gt candidateB_pos) hb0.symm
    · subst j
      rw [hqinner]
      intro hz
      have hr := hinner i
      rw [hz] at hr
      have hr0 : (0 : ℝ) = candidateInnerRadius := by simpa using hr
      exact (ne_of_gt candidateInnerRadius_pos) hr0.symm
    · subst j
      rw [hqright]
      intro hz
      have hb := houterRadius (u i + 1)
      rw [hz] at hb
      have hb0 : (0 : ℝ) = candidateB := by simpa using hb
      exact (ne_of_gt candidateB_pos) hb0.symm
  have hpolar : ∀ i, planeComplex (qAlt i) =
      ((‖qAlt i‖ : ℝ) : ℂ) *
        (Real.cos (θ i) + Real.sin (θ i) * Complex.I) := by
    intro j
    rcases alternating_position_complete j with ⟨i, hj⟩ | ⟨i, hj⟩ | ⟨i, hj⟩
    · subst j
      rw [hqleft i]
      change planeComplex (q (o (u i))) =
        ((‖q (o (u i))‖ : ℝ) : ℂ) *
          (Real.cos (terminalAlternatingLift ψ u φ (alternatingLeft i)) +
            Real.sin (terminalAlternatingLift ψ u φ (alternatingLeft i)) * Complex.I)
      rw [terminalAlternatingLift_left]
      exact planeComplex_eq_realPolar _ _ (Or.inl rfl)
    · subst j
      rw [hqinner i]
      change planeComplex (q (ix i)) =
        ((‖q (ix i)‖ : ℝ) : ℂ) *
          (Real.cos (terminalAlternatingLift ψ u φ (alternatingInner i)) +
            Real.sin (terminalAlternatingLift ψ u φ (alternatingInner i)) * Complex.I)
      rw [terminalAlternatingLift_inner]
      exact planeComplex_eq_realPolar _ _ (hlift i)
    · subst j
      rw [hqright i]
      change planeComplex (q (o (u i + 1))) =
        ((‖q (o (u i + 1))‖ : ℝ) : ℂ) *
          (Real.cos (terminalAlternatingLift ψ u φ (alternatingRight i)) +
            Real.sin (terminalAlternatingLift ψ u φ (alternatingRight i)) * Complex.I)
      have hθ : (if u i = Fin.last 9 then ψ 0 + 2 * Real.pi
          else ψ (u i + 1)) = polarArg (q (o (u i + 1))) ∨
          (if u i = Fin.last 9 then ψ 0 + 2 * Real.pi
            else ψ (u i + 1)) = polarArg (q (o (u i + 1))) + 2 * Real.pi := by
        by_cases hlast : u i = Fin.last 9
        · right
          have hzero : u i + 1 = (0 : Fin 10) := by simp [hlast]
          simp only [if_pos hlast]
          rw [hzero]
        · left
          have hlast9 : u i ≠ (9 : Fin 10) := by
            simpa [Fin.last] using hlast
          simp [hlast9, ψ]
      rw [terminalAlternatingLift_right]
      exact planeComplex_eq_realPolar _ _ hθ
  obtain ⟨a, harg, hcut⟩ :=
    exists_rotation_with_strictPolarArg_of_angular_lift qAlt θ hθmono hθspan
      hnonzero hpolar
  let r : Fin 15 → Plane := fun i => planeRotation a (qAlt i)
  have hrCong : CenteredCongruent15 r qAlt := by
    refine ⟨Equiv.refl _, planeRotation a, ?_⟩
    intro i
    rfl
  have hr : r ∈ FeasibleSet15 candidateB :=
    feasible_of_centeredCongruent15 r qAlt candidateB hrCong hqAlt
  have hnorm (i : Fin 15) : ‖r i‖ = ‖qAlt i‖ := by
    exact (planeRotation a).norm_map (qAlt i)
  have hBmargin : (17 / 5 : ℝ) < candidateB := by
    linarith [candidateB_local_bounds.1]
  have hleft : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingLeft i)‖ := by
    intro i
    rw [hnorm, hqleft i, houterRadius]
    exact hBmargin
  have hright : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingRight i)‖ := by
    intro i
    rw [hnorm, hqright i, houterRadius]
    exact hBmargin
  have hinnerLo : ∀ i, (1697 / 1000 : ℝ) < ‖r (alternatingInner i)‖ := by
    intro i
    rw [hnorm, hqinner i, hinner i]
    exact candidateInnerRadius_local_bounds.1
  have hinnerHi : ∀ i, ‖r (alternatingInner i)‖ < (853 / 500 : ℝ) := by
    intro i
    rw [hnorm, hqinner i, hinner i]
    exact candidateInnerRadius_local_bounds.2
  exact ⟨r, hr, harg, hcut, hleft, hright, hinnerLo, hinnerHi⟩

/-- The candidate itself is terminal for the one-center boundary replacement
relation. Its component rank is exactly ten: it contains the candidate with
ten boundary centers, and no feasible component can exceed ten. -/
theorem candidate_is_terminal_for_component_ascent :
    ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB
        ⟨Candidate.pointAtSeparationTwo, candidate_mem_FeasibleSet15⟩ q := by
  let p : FeasiblePacking15 candidateB :=
    ⟨Candidate.pointAtSeparationTwo, candidate_mem_FeasibleSet15⟩
  have hrank : componentRank candidateB p = 10 := by
    have hlower := componentRank_max candidateB p p.1
      (mem_connectedComponentIn p.2)
    rw [Candidate.boundarySet_pointAtSeparationTwo_card] at hlower
    have hupper := componentRank_le_ten candidateB candidateB_pos
      (le_refl _) p
    omega
  rintro ⟨q, hstep⟩
  have hinc := componentBoundaryStep_rank_increase candidateB p q hstep
  have hupper := componentRank_le_ten candidateB candidateB_pos
    (le_refl _) q
  rw [hrank] at hinc
  omega

/-- The terminal equality classification of the candidate component supplies
an explicit feasible reference in the local rigidity chart. -/
theorem exists_candidate_localAlternatingReference :
    ∃ r, r ∈ FeasibleSet15 candidateB ∧
      StrictMono (fun i => polarArg (r i)) ∧
      (∀ i, planeComplex (r i) ∈ Complex.slitPlane) ∧
      (∀ i, (17 / 5 : ℝ) < ‖r (alternatingLeft i)‖) ∧
      (∀ i, (17 / 5 : ℝ) < ‖r (alternatingRight i)‖) ∧
      (∀ i, (1697 / 1000 : ℝ) < ‖r (alternatingInner i)‖) ∧
      (∀ i, ‖r (alternatingInner i)‖ < (853 / 500 : ℝ)) := by
  let p : FeasiblePacking15 candidateB :=
    ⟨Candidate.pointAtSeparationTwo, candidate_mem_FeasibleSet15⟩
  obtain ⟨q, hq, ix, o, u, φ, hix, ho, hparity, hinner, houter,
      houterComplete, hinnerComplete, hlift, _hgap, hempty, hoccupied,
      hphase⟩ :=
    terminal_component_actual_angular_equalities p
      candidate_is_terminal_for_component_ascent
  have hqFeasible : q ∈ FeasibleSet15 candidateB :=
    (connectedComponentIn_subset (FeasibleSet15 candidateB) p.1) hq
  exact exists_localAlternatingReference_of_terminalData q ix o u φ
    hix ho hparity hinner houter houterComplete hinnerComplete hlift
    hempty hoccupied hphase hqFeasible

end CP15
