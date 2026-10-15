import CP15.M3K10
import CP15.M3K8Closure

open scoped InnerProductSpace

namespace CP15

/-- The complete `m = 3` exclusion for a selected packing at the
candidate radius: all boundary counts `K ≤ 10` are covered. -/
theorem m3_impossible_at_K_le_ten
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hK : (boundarySet p b).card ≤ 10)
    (hm3 : 3 ≤ (nonOuterIndices p b).card) : False := by
  by_cases hK8 : (boundarySet p b).card ≤ 8
  · exact m3_impossible_at_K_le_8 p b hb hbB hpack hD hFcap
      hFsmall hblock hK8 hm3
  by_cases hK9 : (boundarySet p b).card = 9
  · exact m3_impossible_at_K9 p b hb hbB hpack hD hFcap
      hFsmall hblock hK9 hm3
  have hK10 : (boundarySet p b).card = 10 := by omega
  exact m3_impossible_at_K10 p b hb hbB hpack hD hFcap
    hFsmall hblock hK10.ge hm3

/-- The selected representative has at most two centers that do not
touch the boundary. This is the first unconditional `m ≤ 2` theorem. -/
theorem exists_optimal_selected_with_m_le_two :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      (nonOuterIndices p b).card ≤ 2 ∧
      (boundarySet p b).card ≤ 10 := by
  obtain ⟨b, p, hbB, hopt, hp, hs, hD, hblock, hFcap, hFsmall, _⟩ :=
    exists_optimal_selected_full
  have hb : 2 < b := centerFeasible_radius_gt_two hopt.1
  have hK := boundary_count_le_ten p b (by linarith) hbB hs
  have hm : (nonOuterIndices p b).card ≤ 2 := by
    by_contra hnot
    exact m3_impossible_at_K_le_ten p b hb hbB ⟨hp, hs⟩ hD
      hFcap hFsmall hblock hK (by omega)
  exact ⟨b, p, hbB, hopt, hp, hs, hm, hK⟩

end CP15
