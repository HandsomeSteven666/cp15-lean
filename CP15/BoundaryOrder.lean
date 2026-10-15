import CP15.OuterRingOrder

namespace CP15

/-- An index carrying a proof that its center lies on the outer circle. -/
abbrev BoundaryIndex (p : Fin 15 → Plane) (b : ℝ) :=
  {i : Fin 15 // ‖p i‖ = b}

/-- Polar argument is injective on the boundary index type of any separated
packing. This is the sole geometric input for ordering the boundary points. -/
theorem boundaryIndex_arg_injective (p : Fin 15 → Plane) (b : ℝ)
    (hsep : Separated p 2) :
    Function.Injective (fun i : BoundaryIndex p b => polarArg (p i.val)) := by
  intro i j hij
  apply Subtype.ext
  exact boundary_polarArg_injective p b hsep i.val j.val i.property j.property hij

/-- The subtype count used for angle sorting is exactly the `K` count used
in the extremal selection. -/
theorem boundaryIndex_card_eq_boundarySet_card (p : Fin 15 → Plane) (b : ℝ) :
    Fintype.card (BoundaryIndex p b) = (boundarySet p b).card := by
  classical
  simp [BoundaryIndex, boundarySet, Fintype.card_subtype]

/-- The finite set of arguments of actual boundary centers. -/
noncomputable def boundaryAngles (p : Fin 15 → Plane) (b : ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun i : BoundaryIndex p b => polarArg (p i.val))

theorem boundaryAngles_card (p : Fin 15 → Plane) (b : ℝ)
    (hsep : Separated p 2) :
    (boundaryAngles p b).card = (boundarySet p b).card := by
  classical
  rw [boundaryAngles, Finset.card_image_of_injective _
    (boundaryIndex_arg_injective p b hsep)]
  simpa using boundaryIndex_card_eq_boundarySet_card p b

theorem boundaryAngles_mem (p : Fin 15 → Plane) (b θ : ℝ) :
    θ ∈ boundaryAngles p b ↔
      ∃ i : BoundaryIndex p b, polarArg (p i.val) = θ := by
  classical
  simp [boundaryAngles]

/-- Every actual boundary center occurs at one index of the sorted-angle
embedding. -/
theorem boundary_center_has_sorted_index (p : Fin 15 → Plane) (b : ℝ)
    (j : Fin 15) (hj : ‖p j‖ = b) :
    ∃ u : Fin (boundaryAngles p b).card,
      (boundaryAngles p b).orderEmbOfFin rfl u = polarArg (p j) := by
  classical
  let s := boundaryAngles p b
  have hjmem : polarArg (p j) ∈ s := by
    apply (boundaryAngles_mem p b (polarArg (p j))).2
    exact ⟨⟨j, hj⟩, rfl⟩
  have hrange : polarArg (p j) ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hjmem
  obtain ⟨u, hu⟩ := hrange
  exact ⟨u, hu⟩

/-- A canonical increasing list of boundary angles. Injectivity of polar
argument lets us recover a unique boundary center from each entry. The list
construction makes no assumption about cyclic gaps or contact patterns. -/
theorem exists_boundary_order (p : Fin 15 → Plane) (b : ℝ)
    (hsep : Separated p 2) :
    ∃ l : List ℝ,
      l.Nodup ∧
      (∀ θ : ℝ, θ ∈ l ↔ ∃ i : BoundaryIndex p b, polarArg (p i.val) = θ) ∧
      l.length = Fintype.card (BoundaryIndex p b) ∧
      l.Pairwise (· < ·) := by
  classical
  let f : BoundaryIndex p b → ℝ := fun i => polarArg (p i.val)
  have hf : Function.Injective f := boundaryIndex_arg_injective p b hsep
  let angles : Finset ℝ := Finset.univ.image f
  let l : List ℝ := angles.sort
  refine ⟨l, ?_, ?_, ?_, ?_⟩
  · exact Finset.sort_nodup _ _
  · intro θ
    simp [l, angles, f]
  · simp [l, angles, Finset.card_image_of_injective _ hf]
  · exact List.sortedLT_iff_pairwise.mp
      ((Finset.pairwise_sort angles (· ≤ ·)).sortedLE.sortedLT_of_nodup
        (Finset.sort_nodup angles (· ≤ ·)))

end CP15
