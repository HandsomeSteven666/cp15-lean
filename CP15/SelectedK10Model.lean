import CP15.OccupiedGapModel

namespace CP15

set_option maxHeartbeats 0

noncomputable def K10OuterAngles (p : Fin 15 → Plane) (b : ℝ)
    (hcard : (boundaryAngles p b).card = 10) (i : Fin 10) : ℝ :=
  (boundaryAngles p b).orderEmbOfFin rfl (Fin.cast hcard.symm i)

theorem K10_outer_gap_cast (p : Fin 15 → Plane) (b : ℝ)
    (hcard : (boundaryAngles p b).card = 10) (hs : 2 ≤ (boundaryAngles p b).card)
    (i : Fin 10) :
    nextBoundaryGap p b hs (Fin.cast hcard.symm i) = cyclicAngleGap (K10OuterAngles p b hcard) i := by
  fin_cases i <;> norm_num [nextBoundaryGap, cyclicAngleGap, K10OuterAngles,
    Fin.cast, hcard] <;> ring

theorem SelectedPacking15.K10_outer_angle_lower
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hcard : (boundaryAngles p b).card = 10) :
    ∀ i, outerAlpha b ≤ cyclicAngleGap (K10OuterAngles p b hcard) i := by
  classical
  let ψ := K10OuterAngles p b hcard
  have hmem (i : Fin 10) : ψ i ∈ boundaryAngles p b :=
    Finset.orderEmbOfFin_mem (boundaryAngles p b) rfl (Fin.cast hcard.symm i)
  have hpoints (i : Fin 10) := (boundaryAngles_mem p b (ψ i)).mp (hmem i)
  choose o ho using hpoints
  have hmono : StrictMono ψ := by
    intro i j hij
    apply (boundaryAngles p b).orderEmbOfFin rfl |>.strictMono
    exact hij
  have hrange (i : Fin 10) : -Real.pi < ψ i ∧ ψ i ≤ Real.pi := by
    rw [← ho i]
    exact polarArg_range _
  have hinj : Function.Injective o := by
    intro i j heq
    apply hmono.injective
    rw [← ho i, ← ho j, heq]
  have hb : 1 < b := by linarith [centerFeasible_radius_gt_two h.optimal.1]
  intro i
  have hne : i ≠ i + 1 := by fin_cases i <;> decide
  have hval : (o i).val ≠ (o (i + 1)).val := by
    intro heq
    exact hne (hinj (Subtype.ext heq))
  have hh := directed_clearance_angle_lower (p (o i).val) (p (o (i + 1)).val)
    (cyclicAngleGap ψ i) (by rw [(o i).property]; linarith)
    (by rw [(o (i + 1)).property]; linarith) (h.separated _ _ hval)
    (cyclicAngleGap_nonneg ψ hmono hrange i)
    (cyclicAngleGap_cos (fun i => p (o i).val) ψ ho i)
  rw [(o i).property, (o (i + 1)).property, contactAngle_diagonal_eq_outerAlpha b hb] at hh
  exact hh

/-- The complete scalar model is supplied by the actual selected packing.
Its five distinct occupied gaps come from the proved geometric assignment,
and every empty-gap count and full-turn angle is retained. -/
theorem SelectedPacking15.K10m0_cyclic_model_actual
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10) (hm : (nonOuterIndices p b).card = 0) :
    ∃ ix : Fin 5 → Fin 15, ∃ u : Fin 5 → Fin 10,
      ∃ φ : Fin 5 → ℝ, ∃ ψ : Fin 10 → ℝ,
      Function.Injective ix ∧ StrictMono u ∧
      (∀ i, ‖p (ix i)‖ < b) ∧
      (∀ i, φ i = polarArg (p (ix i)) ∨
        φ i = polarArg (p (ix i)) + 2 * Real.pi) ∧
      (∀ i, ψ (u i) + contactAngle b ‖p (ix i)‖ ≤ φ i) ∧
      (∀ i, φ i ≤ ψ (u i) + cyclicAngleGap ψ (u i) -
        contactAngle b ‖p (ix i)‖) ∧
      (∀ k, outerAlpha b ≤ cyclicAngleGap ψ k) ∧
      StrictMono ψ ∧
      (∀ k, ψ k ∈ boundaryAngles p b) ∧
      CyclicInnerModel b (fun i => ‖p (ix i)‖)
        (occupiedEmptyCount u) (cyclicAngleGap φ) := by
  classical
  have hcard : (boundaryAngles p b).card = 10 := (boundaryAngles_card p b h.separated).trans hK
  have hs : 2 ≤ (boundaryAngles p b).card := by omega
  have hpart := boundary_nonOuter_touching_card_partition p b h.inDisk
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 5) ≤ (touchingInnerSet p b).card by simp; omega)
  have hd (i : Fin 5) : ‖p (e i)‖ < b ∧ TouchesOuter p b (e i) := by
    have hx := he ⟨i, rfl⟩
    simpa [touchingInnerSet] using hx
  obtain ⟨charge, θ, δ, hcharge, hcontact⟩ :=
    h.K10_injective_touching_gap_assignment hK e e.injective (fun i => (hd i).1)
      (fun i => (hd i).2) hs
  let src := Tuple.sort charge
  let ix : Fin 5 → Fin 15 := fun i => e (src i)
  let u : Fin 5 → Fin 10 := fun i => Fin.cast hcard (charge (src i))
  let φ : Fin 5 → ℝ := fun i => θ (src i)
  let ψ := K10OuterAngles p b hcard
  have hix : Function.Injective ix := e.injective.comp src.injective
  have huMono : Monotone u := by
    intro i j hij
    exact Tuple.monotone_sort charge hij
  have huInj : Function.Injective u := by
    intro i j hij
    apply src.injective
    apply hcharge
    apply Fin.ext
    exact congrArg (fun x : Fin 10 => x.val) hij
  have hu := huMono.strictMono_of_injective huInj
  have hr (i : Fin 5) : ‖p (ix i)‖ ∈ Set.Icc (123 / 100 : ℝ) (9 / 4) := by
    exact ⟨(h.touching_radius_gt_123_div_100 _ (hd (src i)).1 (hd (src i)).2).le,
      (h.K10_touching_radius_lt_nine_fourths hK _ (hd (src i)).1 (hd (src i)).2).le⟩
  have hsame (i : Fin 5) : ψ (u i) =
      (boundaryAngles p b).orderEmbOfFin rfl (charge (src i)) := by
    simp [ψ, u, K10OuterAngles]
  have hgap (i : Fin 5) : nextBoundaryGap p b hs (charge (src i)) = cyclicAngleGap ψ (u i) := by
    simpa [u, ψ] using K10_outer_gap_cast p b hcard hs (u i)
  have hphase (i : Fin 5) : φ i = polarArg (p (ix i)) ∨ φ i = polarArg (p (ix i)) + 2 * Real.pi :=
    (hcontact (src i)).1
  have hleft (i : Fin 5) : ψ (u i) + contactAngle b ‖p (ix i)‖ ≤ φ i := by
    have hc := hcontact (src i)
    rw [hsame i]
    have hs' := hc.2.2.2.1
    rw [hc.2.1] at hs'
    rcases hc.2.2.2.2 with hl | hr
    · simpa [φ, ix, hc.2.1] using hl.ge
    · dsimp [φ, ix]
      rw [hr, hc.2.1]
      linarith
  have hright (i : Fin 5) : φ i ≤ ψ (u i) + cyclicAngleGap ψ (u i) - contactAngle b ‖p (ix i)‖ := by
    have hc := hcontact (src i)
    rw [hsame i, ← hgap i]
    have hs' := hc.2.2.2.1
    rw [hc.2.1] at hs'
    rcases hc.2.2.2.2 with hl | hr
    · dsimp [φ, ix]
      rw [hl, hc.2.1]
      linarith
    · simpa [φ, ix, hc.2.1] using hr.le
  have hb : 0 < b := by linarith [centerFeasible_radius_gt_two h.optimal.1]
  have hα0 : 0 ≤ outerAlpha b := by
    unfold outerAlpha
    exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (by positivity))
  have hcost := h.touching_cost_budget (by omega) ix hix
    (fun i => (hd (src i)).1) (fun i => (hd (src i)).2)
  have hmax (x : ℝ) : max (57588 / 100000 : ℝ) x =
      57588 / 100000 + max 0 (x - 57588 / 100000) := by
    by_cases hx : (57588 / 100000 : ℝ) ≤ x
    · rw [max_eq_right hx, max_eq_right (by linarith)]
      ring
    · rw [max_eq_left (le_of_not_ge hx), max_eq_left (by linarith)]
      ring
  have hcost' : 5 * (57588 / 100000 : ℝ) +
      (∑ i, max (57588 / 100000 : ℝ) (2 * contactAngle b ‖p (ix i)‖)) ≤ 2 * Real.pi := by
    simp only [hmax, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    simp only [hK, Nat.cast_ofNat] at hcost
    linarith
  have hα := h.K10_outer_angle_lower hcard
  have hψmono : StrictMono ψ := by
    intro i j hij
    exact (boundaryAngles p b).orderEmbOfFin rfl |>.strictMono hij
  have hψmem (k : Fin 10) : ψ k ∈ boundaryAngles p b :=
    Finset.orderEmbOfFin_mem (boundaryAngles p b) rfl (Fin.cast hcard.symm k)
  exact ⟨ix, u, φ, ψ, hix, hu, (fun i => (hd (src i)).1),
    hphase, hleft, hright, hα, hψmono, hψmem,
    occupied_gap_model (fun i => p (ix i)) b ψ u φ hu
      (fun i j hij => h.separated _ _ (hix.ne hij)) hr hα0
      hα hphase hleft hright hcost'⟩

/-- The scalar model remains available to the endpoint certificate. -/
theorem SelectedPacking15.K10m0_cyclic_model
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (hm : (nonOuterIndices p b).card = 0) :
    ∃ r : Fin 5 → ℝ, ∃ empty : Fin 5 → ℕ, ∃ g : Fin 5 → ℝ,
      CyclicInnerModel b r empty g := by
  obtain ⟨ix, u, φ, ψ, _, _, _, _, _, _, _, _, _, hmodel⟩ :=
    h.K10m0_cyclic_model_actual hK hm
  exact ⟨_, _, _, hmodel⟩

end CP15
