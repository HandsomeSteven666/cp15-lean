import CP15.K10EndpointEquality

namespace CP15

/-- The five indexed inner centers exhaust all nonboundary centers when
exactly ten of the fifteen centers lie on the container circle. -/
theorem actual_inner_indices_complete
    (p : Fin 15 → Plane) (b : ℝ)
    (hK : (boundarySet p b).card = 10)
    (ix : Fin 5 → Fin 15) (hix : Function.Injective ix)
    (hinner : ∀ i, ‖p (ix i)‖ < b) :
    ∀ j, ‖p j‖ < b → ∃ i, ix i = j := by
  classical
  let I : Finset (Fin 15) := Finset.univ.image ix
  have hIcard : I.card = 5 := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ hix]
    simp
  have hdisj : Disjoint I (boundarySet p b) := by
    apply Finset.disjoint_left.mpr
    intro j hjI hjB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hjI
    have hh : ‖p (ix i)‖ = b := by simpa [boundarySet] using hjB
    linarith [hinner i]
  have hunion : I ∪ boundarySet p b = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.subset_univ _
    · rw [Finset.card_union_of_disjoint hdisj, hIcard, hK]
      simp
  intro j hj
  have hjI : j ∈ I := by
    have hjU : j ∈ I ∪ boundarySet p b := by
      rw [hunion]
      exact Finset.mem_univ j
    rcases Finset.mem_union.mp hjU with h | h
    · exact h
    · have heq : ‖p j‖ = b := by simpa [boundarySet] using h
      linarith
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hjI
  exact ⟨i, hi⟩

/-- The ten sorted boundary angles retained by the actual gap model
enumerate the ten boundary centers of the original packing bijectively. -/
theorem actual_boundary_order_of_gap_data
    (p : Fin 15 → Plane) (b : ℝ)
    (hK : (boundarySet p b).card = 10)
    (ψ : Fin 10 → ℝ) (hψmono : StrictMono ψ)
    (hψmem : ∀ k, ψ k ∈ boundaryAngles p b) :
    ∃ o : Fin 10 → Fin 15,
      Function.Injective o ∧
      (∀ k, ‖p (o k)‖ = b ∧ polarArg (p (o k)) = ψ k) ∧
      (∀ j, ‖p j‖ = b → ∃ k, o k = j) := by
  classical
  have hex (k : Fin 10) :
      ∃ j : Fin 15, ‖p j‖ = b ∧ polarArg (p j) = ψ k := by
    obtain ⟨j, hj⟩ := (boundaryAngles_mem p b (ψ k)).mp (hψmem k)
    exact ⟨j.val, j.property, hj⟩
  choose o ho using hex
  have hinj : Function.Injective o := by
    intro i j hij
    apply hψmono.injective
    rw [← (ho i).2, ← (ho j).2, hij]
  have hsub : Finset.univ.image o ⊆ boundarySet p b := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    simp [boundarySet, (ho k).1]
  have hcard : (Finset.univ.image o).card = 10 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have heq : Finset.univ.image o = boundarySet p b := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard, hK]
  refine ⟨o, hinj, ho, ?_⟩
  intro j hj
  have hjmem : j ∈ boundarySet p b := by simp [boundarySet, hj]
  rw [← heq] at hjmem
  obtain ⟨k, _, hkj⟩ := Finset.mem_image.mp hjmem
  exact ⟨k, hkj⟩

/-- At an alternating five-gap occupancy, equality in the total angular
budget forces every occupied outer gap and every empty gap to attain its
respective lower bound. -/
theorem alternating_outer_gap_equality
    (g : Fin 10 → ℝ) (u : Fin 5 → Fin 10)
    (a : Fin 2) (α γ : ℝ)
    (hu : ∀ i, (u i).val = a.val + 2 * i.val)
    (hα : ∀ k, α ≤ g k)
    (hocc : ∀ i, 2 * γ ≤ g (u i))
    (hsum : (∑ k, g k) = 5 * α + 10 * γ) :
    (∀ i, g (u i) = 2 * γ) ∧
      (∀ k, (∀ i, u i ≠ k) → g k = α) := by
  have ho0 := hocc 0
  have ho1 := hocc 1
  have ho2 := hocc 2
  have ho3 := hocc 3
  have ho4 := hocc 4
  have ha0 := hα 0; have ha1 := hα 1
  have ha2 := hα 2; have ha3 := hα 3
  have ha4 := hα 4; have ha5 := hα 5
  have ha6 := hα 6; have ha7 := hα 7
  have ha8 := hα 8; have ha9 := hα 9
  have hs : g 0 + g 1 + g 2 + g 3 + g 4 +
      g 5 + g 6 + g 7 + g 8 + g 9 = 5 * α + 10 * γ := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  fin_cases a
  · have hu0 : u 0 = 0 := Fin.ext (by simpa using hu 0)
    have hu1 : u 1 = 2 := Fin.ext (by simpa using hu 1)
    have hu2 : u 2 = 4 := Fin.ext (by simpa using hu 2)
    have hu3 : u 3 = 6 := Fin.ext (by simpa using hu 3)
    have hu4 : u 4 = 8 := Fin.ext (by simpa using hu 4)
    rw [hu0] at ho0
    rw [hu1] at ho1
    rw [hu2] at ho2
    rw [hu3] at ho3
    rw [hu4] at ho4
    have hg0 : g 0 = 2 * γ := by linarith
    have hg2 : g 2 = 2 * γ := by linarith
    have hg4 : g 4 = 2 * γ := by linarith
    have hg6 : g 6 = 2 * γ := by linarith
    have hg8 : g 8 = 2 * γ := by linarith
    have hg1 : g 1 = α := by linarith
    have hg3 : g 3 = α := by linarith
    have hg5 : g 5 = α := by linarith
    have hg7 : g 7 = α := by linarith
    have hg9 : g 9 = α := by linarith
    constructor
    · intro i
      fin_cases i <;> simp [hu0, hu1, hu2, hu3, hu4,
        hg0, hg2, hg4, hg6, hg8]
    · intro k hk
      fin_cases k
      all_goals first
        | exact hg1
        | exact hg3
        | exact hg5
        | exact hg7
        | exact hg9
        | exact False.elim (hk 0 hu0)
        | exact False.elim (hk 1 hu1)
        | exact False.elim (hk 2 hu2)
        | exact False.elim (hk 3 hu3)
        | exact False.elim (hk 4 hu4)
  · have hu0 : u 0 = 1 := Fin.ext (by simpa using hu 0)
    have hu1 : u 1 = 3 := Fin.ext (by simpa using hu 1)
    have hu2 : u 2 = 5 := Fin.ext (by simpa using hu 2)
    have hu3 : u 3 = 7 := Fin.ext (by simpa using hu 3)
    have hu4 : u 4 = 9 := Fin.ext (by simpa using hu 4)
    rw [hu0] at ho0
    rw [hu1] at ho1
    rw [hu2] at ho2
    rw [hu3] at ho3
    rw [hu4] at ho4
    have hg1 : g 1 = 2 * γ := by linarith
    have hg3 : g 3 = 2 * γ := by linarith
    have hg5 : g 5 = 2 * γ := by linarith
    have hg7 : g 7 = 2 * γ := by linarith
    have hg9 : g 9 = 2 * γ := by linarith
    have hg0 : g 0 = α := by linarith
    have hg2 : g 2 = α := by linarith
    have hg4 : g 4 = α := by linarith
    have hg6 : g 6 = α := by linarith
    have hg8 : g 8 = α := by linarith
    constructor
    · intro i
      fin_cases i <;> simp [hu0, hu1, hu2, hu3, hu4,
        hg1, hg3, hg5, hg7, hg9]
    · intro k hk
      fin_cases k
      all_goals first
        | exact hg0
        | exact hg2
        | exact hg4
        | exact hg6
        | exact hg8
        | exact False.elim (hk 0 hu0)
        | exact False.elim (hk 1 hu1)
        | exact False.elim (hk 2 hu2)
        | exact False.elim (hk 3 hu3)
        | exact False.elim (hk 4 hu4)

/-- Exact outer gaps and inner angular phases for the actual selected
packing. Every one of the fifteen angular inequalities is tight. -/
theorem SelectedPacking15.K10m0_actual_gap_equalities
    {p : Fin 15 → Plane} (h : SelectedPacking15 p candidateB)
    (hK : (boundarySet p candidateB).card = 10)
    (hm : (nonOuterIndices p candidateB).card = 0) :
    ∃ ix : Fin 5 → Fin 15, ∃ u : Fin 5 → Fin 10,
      ∃ φ : Fin 5 → ℝ, ∃ ψ : Fin 10 → ℝ,
      Function.Injective ix ∧ StrictMono u ∧
      (∃ a : Fin 2, ∀ i, (u i).val = a.val + 2 * i.val) ∧
      (∀ i, ‖p (ix i)‖ < candidateB) ∧
      (∀ i, ‖p (ix i)‖ = candidateInnerRadius) ∧
      (∀ i, φ i = polarArg (p (ix i)) ∨
        φ i = polarArg (p (ix i)) + 2 * Real.pi) ∧
      (∀ i, cyclicAngleGap φ i = 2 * Real.pi / 5) ∧
      (∀ i, cyclicAngleGap ψ (u i) =
        2 * contactAngle candidateB candidateInnerRadius) ∧
      (∀ k, (∀ i, u i ≠ k) → cyclicAngleGap ψ k = outerAlpha candidateB) ∧
      (∀ i, φ i = ψ (u i) +
        contactAngle candidateB candidateInnerRadius) ∧
      StrictMono ψ ∧
      (∀ k, ψ k ∈ boundaryAngles p candidateB) := by
  obtain ⟨ix, u, φ, ψ, hix, hu, hinner, hr, he, hg,
    hlift, hleft, hright, hα, hψmono, hψmem⟩ :=
    h.K10m0_actual_inner_equalities hK hm
  obtain ⟨a, ha⟩ := occupiedEmptyCount_one_alternating u he
  have hocc (i : Fin 5) :
      2 * contactAngle candidateB candidateInnerRadius ≤
        cyclicAngleGap ψ (u i) := by
    have hl := hleft i
    have hh := hright i
    rw [hr i] at hl hh
    linarith
  have hsum : (∑ k, cyclicAngleGap ψ k) =
      5 * outerAlpha candidateB +
        10 * contactAngle candidateB candidateInnerRadius := by
    rw [cyclicAngleGap_sum]
    linarith [candidate_outer_inner_angle_balance]
  obtain ⟨hoccupied, hempty⟩ :=
    alternating_outer_gap_equality (cyclicAngleGap ψ) u a
      (outerAlpha candidateB)
      (contactAngle candidateB candidateInnerRadius)
      ha hα hocc hsum
  have hphase (i : Fin 5) : φ i = ψ (u i) +
      contactAngle candidateB candidateInnerRadius := by
    have hl := hleft i
    have hh := hright i
    rw [hr i] at hl hh
    have hgap := hoccupied i
    linarith
  exact ⟨ix, u, φ, ψ, hix, hu, ⟨a, ha⟩, hinner, hr, hlift, hg,
    hoccupied, hempty, hphase,
    hψmono, hψmem⟩

end CP15
