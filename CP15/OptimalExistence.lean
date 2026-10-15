import CP15.CompactSelection

namespace CP15

private theorem fin15_univ_nonempty :
    (Finset.univ : Finset (Fin 15)).Nonempty := ⟨0, by simp⟩

/-- The maximum center radius of a fixed fifteen-point configuration. -/
noncomputable def maxRadius (p : Fin 15 → Plane) : ℝ :=
  Finset.univ.sup' fin15_univ_nonempty (fun i => ‖p i‖)

theorem maxRadius_continuous : Continuous maxRadius := by
  unfold maxRadius
  apply Continuous.finset_sup'_apply fin15_univ_nonempty
  intro i hi
  exact (continuous_apply i).norm

theorem inDisk_iff_maxRadius_le (p : Fin 15 → Plane) (b : ℝ) :
    InDisk b p ↔ maxRadius p ≤ b := by
  constructor
  · intro hp
    unfold maxRadius
    apply Finset.sup'_le
    intro i hi
    exact hp i
  · intro hmax i
    exact (Finset.le_sup' (f := fun j : Fin 15 => ‖p j‖)
      (Finset.mem_univ i)).trans hmax

/-- An optimal center radius is attained whenever one feasible upper radius
is supplied. The proof minimizes the continuous maximum-radius function on
the compact feasible set inside that upper disk. -/
theorem centerOptimal_exists_of_feasible {B : ℝ}
    (hB : CenterFeasible 15 B) :
    ∃ b : ℝ, b ≤ B ∧ CenterOptimal 15 b := by
  let T := FeasibleWithBoundary B (∅ : Finset (Fin 15))
  have hTcompact : IsCompact T := isCompact_feasibleWithBoundary B ∅
  have hTnonempty : T.Nonempty := by
    rcases hB with ⟨p, hp, hs⟩
    exact ⟨p, hp, hs, by simp⟩
  obtain ⟨p, hpT, hmin⟩ :=
    hTcompact.exists_isMinOn hTnonempty maxRadius_continuous.continuousOn
  let b := maxRadius p
  have hbB : b ≤ B := (inDisk_iff_maxRadius_le p B).1 hpT.1
  have hpAtB : InDisk b p := (inDisk_iff_maxRadius_le p b).2 le_rfl
  refine ⟨b, hbB, ⟨p, hpAtB, hpT.2.1⟩, ?_⟩
  intro c hc
  rcases hc with ⟨q, hqc, hqs⟩
  by_cases hcB : c ≤ B
  · have hqT : q ∈ T := by
      refine ⟨?_, hqs, by simp⟩
      intro i
      exact (hqc i).trans hcB
    exact (hmin hqT).trans ((inDisk_iff_maxRadius_le q c).1 hqc)
  · exact hbB.trans (le_of_lt (lt_of_not_ge hcB))

end CP15
