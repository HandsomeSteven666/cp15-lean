import CP15.Replacement

namespace CP15

/-- At any feasible radius, there is a feasible configuration maximizing the
finite number of centers on the boundary. No compactness is needed here. -/
theorem exists_maxBoundaryCount {n : ℕ} {b : ℝ}
    (h : CenterFeasible n b) :
    ∃ p : Fin n → Plane,
      InDisk b p ∧ Separated p 2 ∧ MaxBoundaryCount p b := by
  let S : Set ℕ :=
    {k | ∃ p : Fin n → Plane,
      InDisk b p ∧ Separated p 2 ∧ (boundarySet p b).card = k}
  have hSfinite : S.Finite := by
    apply (Set.finite_Icc 0 n).subset
    intro k hk
    rcases hk with ⟨p, _, _, rfl⟩
    constructor
    · exact Nat.zero_le _
    · simpa [boundarySet] using
        (Finset.card_filter_le (Finset.univ : Finset (Fin n))
          (fun i => ‖p i‖ = b))
  have hSnonempty : S.Nonempty := by
    rcases h with ⟨p, hp, hs⟩
    exact ⟨(boundarySet p b).card, p, hp, hs, rfl⟩
  obtain ⟨k, hkS, hmax⟩ := hSfinite.exists_maximal hSnonempty
  rcases hkS with ⟨p, hp, hs, hcard⟩
  refine ⟨p, hp, hs, ?_⟩
  intro q hq hsq
  by_contra hnot
  have hlt : (boundarySet p b).card < (boundarySet q b).card :=
    Nat.lt_of_not_ge hnot
  have hqS : (boundarySet q b).card ∈ S := ⟨q, hq, hsq, rfl⟩
  have hback := hmax hqS (by omega : k ≤ (boundarySet q b).card)
  omega

theorem exists_maxBoundaryCount_with_inner_cap {n : ℕ} {b : ℝ}
    (hb : 2 < b) (h : CenterFeasible n b) :
    ∃ p : Fin n → Plane,
      InDisk b p ∧ Separated p 2 ∧ MaxBoundaryCount p b ∧
        (∀ i, ‖p i‖ < b → ‖p i‖ < D b) := by
  obtain ⟨p, hp, hs, hmax⟩ := exists_maxBoundaryCount h
  exact ⟨p, hp, hs, hmax,
    inner_cap_of_noBoundaryReplacement p b hb ⟨hp, hs⟩
      (noBoundaryReplacement_of_maxBoundaryCount p b hmax)⟩

end CP15
