import CP15.Selection

namespace CP15

/-- Every attained minimum-radius packing has a boundary center. The
argument chooses an actual maximal radius among the fifteen centers. -/
theorem boundary_exists_of_centerOptimal (p : Fin 15 → Plane) (b : ℝ)
    (hopt : CenterOptimal 15 b)
    (hpack : InDisk b p ∧ Separated p 2) :
    ∃ i : Fin 15, ‖p i‖ = b := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin 15)) (fun j => ‖p j‖)
    (by simp : (Finset.univ : Finset (Fin 15)).Nonempty)
  have hsmaller : CenterFeasible 15 ‖p i‖ := by
    refine ⟨p, ?_, hpack.2⟩
    intro j
    exact hi j (Finset.mem_univ j)
  have hmin := hopt.2 ‖p i‖ hsmaller
  exact ⟨i, le_antisymm (hpack.1 i) hmin⟩

theorem boundary_count_pos_of_centerOptimal (p : Fin 15 → Plane) (b : ℝ)
    (hopt : CenterOptimal 15 b)
    (hpack : InDisk b p ∧ Separated p 2) :
    0 < (boundarySet p b).card := by
  obtain ⟨i, hi⟩ := boundary_exists_of_centerOptimal p b hopt hpack
  exact Finset.card_pos.mpr ⟨i,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

end CP15
