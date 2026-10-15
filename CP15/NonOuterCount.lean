import CP15.FourPoint
import CP15.CandidateConsequences

namespace CP15

/-- The finite index set counted by `m` in the paper argument. -/
noncomputable def nonOuterIndices (p : Fin 15 → Plane) (b : ℝ) :
    Finset (Fin 15) := by
  classical
  exact Finset.univ.filter (fun i => ‖p i‖ < b ∧ ¬TouchesOuter p b i)

/-- A geometric cardinality theorem, independent of optimality and of any
outer-ring ordering. It uses only separation and the strict `F < sqrt 2` cap. -/
theorem nonOuter_count_le_three (p : Fin 15 → Plane) (b : ℝ)
    (hsep : Separated p 2)
    (hcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hF : F b < Real.sqrt 2) :
    (nonOuterIndices p b).card ≤ 3 := by
  classical
  by_contra hcard
  have hfour : Fintype.card (Fin 4) ≤ (nonOuterIndices p b).card := by
    simp
    omega
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hfour
  have hsep4 : Separated (fun k : Fin 4 => p (e k)) 2 := by
    intro i j hij
    exact hsep (e i) (e j) (e.injective.ne hij)
  have hsmall : ∀ k : Fin 4, ‖p (e k)‖ < Real.sqrt 2 := by
    intro k
    have hk : e k ∈ nonOuterIndices p b := he ⟨k, rfl⟩
    have hk' : ‖p (e k)‖ < b ∧ ¬TouchesOuter p b (e k) := by
      simpa [nonOuterIndices] using hk
    exact (hcap (e k) hk'.1 hk'.2).trans_lt hF
  obtain ⟨k, hk⟩ := four_point_disk_obstruction
    (fun k : Fin 4 => p (e k)) hsep4
  exact (not_lt_of_ge hk) (hsmall k)

/-- The paper's `m ≤ 3` reduction is unconditional for the selected optimal
representative. This does not exclude `m = 2` or `m = 3`. -/
theorem exists_optimal_selected_with_m_le_three :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) ∧
      (nonOuterIndices p b).card ≤ 3 := by
  obtain ⟨b, p, hbB, hopt, hp, hs, hD, hF, hFsmall⟩ :=
    exists_optimal_selected_with_small_F
  exact ⟨b, p, hbB, hopt, hp, hs, hD, hF,
    nonOuter_count_le_three p b hs hF hFsmall⟩

end CP15
