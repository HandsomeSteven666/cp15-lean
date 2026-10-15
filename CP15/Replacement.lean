import CP15.Radial

namespace CP15

theorem D_pos {b : ℝ} (hb : 2 < b) : 0 < D b := by
  have hb0 : 0 < b := by linarith
  have hprod : 0 < (b - 2) * (b + 2) :=
    mul_pos (by linarith) (by linarith)
  unfold D
  apply sub_pos.mpr
  apply (div_lt_iff₀ hb0).2
  nlinarith

/-- A local maximality premise. It will have to be derived from the chosen
maximum-boundary representative before the global chain can use this lemma. -/
def NoBoundaryReplacement {n : ℕ} (p : Fin n → Plane) (b : ℝ) : Prop :=
  ∀ i q, ‖p i‖ < b → ‖q‖ = b →
    ¬(InDisk b (Function.update p i q) ∧
      Separated (Function.update p i q) 2)

noncomputable def boundarySet {n : ℕ} (p : Fin n → Plane) (b : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ‖p i‖ = b)

def MaxBoundaryCount {n : ℕ} (p : Fin n → Plane) (b : ℝ) : Prop :=
  ∀ q : Fin n → Plane,
    InDisk b q → Separated q 2 →
      (boundarySet q b).card ≤ (boundarySet p b).card

theorem noBoundaryReplacement_of_maxBoundaryCount {n : ℕ}
    (p : Fin n → Plane) (b : ℝ)
    (hmax : MaxBoundaryCount p b) :
    NoBoundaryReplacement p b := by
  intro i q hi hq hfeas
  let p' := Function.update p i q
  have hset : boundarySet p' b = insert i (boundarySet p b) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [boundarySet, p', hq, ne_of_lt hi]
    · simp [boundarySet, p', hji]
  have hnot : i ∉ boundarySet p b := by
    simp [boundarySet, ne_of_lt hi]
  have hcount := hmax p' hfeas.1 hfeas.2
  rw [hset] at hcount
  simp [hnot] at hcount

theorem radial_replacement_feasible {n : ℕ}
    (p : Fin n → Plane) (i : Fin n) (r b : ℝ) (u : Plane)
    (hb : 2 < b) (hr : 0 < r) (hbr : r < b)
    (hD : D b ≤ r) (hu : ‖u‖ = 1)
    (hpi : p i = r • u)
    (hpack : InDisk b p ∧ Separated p 2)
    (hmax : ∀ j, ‖p j‖ < b → ‖p j‖ ≤ r) :
    InDisk b (Function.update p i (b • u)) ∧
      Separated (Function.update p i (b • u)) 2 := by
  have hb0 : 0 ≤ b := by linarith
  have hq : ‖b • u‖ = b := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0, hu]
  constructor
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using hq.le
    · simpa [Function.update_of_ne hji] using hpack.1 j
  · intro j k hjk
    by_cases hji : j = i
    · subst j
      have hki : k ≠ i := Ne.symm hjk
      simp only [Function.update_self, Function.update_of_ne hki]
      have hold : 2 ≤ dist (r • u) (p k) := by
        simpa [hpi] using hpack.2 i k hjk
      by_cases hk : ‖p k‖ < b
      · exact radial_replace_inner_separated u (p k) r b hr.le hbr hu
          (hmax k hk) hold
      · have houter : ‖p k‖ = b :=
          le_antisymm (hpack.1 k) (le_of_not_gt hk)
        exact radial_replace_outer_separated u (p k) r b hr hbr hu
          houter hD hold
    · by_cases hki : k = i
      · subst k
        have hdist : 2 ≤ dist (b • u) (p j) := by
          have hold : 2 ≤ dist (r • u) (p j) := by
            have h := hpack.2 i j (Ne.symm hji)
            simpa [hpi, dist_comm] using h
          by_cases hj : ‖p j‖ < b
          · exact radial_replace_inner_separated u (p j) r b hr.le hbr hu
              (hmax j hj) hold
          · have houter : ‖p j‖ = b :=
              le_antisymm (hpack.1 j) (le_of_not_gt hj)
            exact radial_replace_outer_separated u (p j) r b hr hbr hu
              houter hD hold
        simpa [Function.update_of_ne hji, dist_comm] using hdist
      · simpa [Function.update_of_ne hji, Function.update_of_ne hki]
          using hpack.2 j k hjk

/-- The full strict inner radial cap, under exactly the local boundary
maximality property needed by the replacement argument. -/
theorem inner_cap_of_noBoundaryReplacement {n : ℕ}
    (p : Fin n → Plane) (b : ℝ)
    (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hno : NoBoundaryReplacement p b) :
    ∀ i, ‖p i‖ < b → ‖p i‖ < D b := by
  intro i hi
  let S : Finset (Fin n) := Finset.univ.filter (fun j => ‖p j‖ < b)
  have hS : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨j, hjS, hmax⟩ := Finset.exists_max_image S (fun k => ‖p k‖) hS
  have hj : ‖p j‖ < b := (Finset.mem_filter.mp hjS).2
  have hmax' : ∀ k, ‖p k‖ < b → ‖p k‖ ≤ ‖p j‖ := by
    intro k hk
    exact hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  by_contra hcap
  have hD : D b ≤ ‖p j‖ :=
    (le_of_not_gt hcap).trans (hmax' i hi)
  let r : ℝ := ‖p j‖
  have hr : 0 < r := (D_pos hb).trans_le hD
  let u : Plane := (1 / r) • p j
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = |1 / r| * r by simp [u, r, norm_smul]]
    rw [abs_of_pos (one_div_pos.mpr hr)]
    field_simp
  have hpi : p j = r • u := by
    change p j = r • ((1 / r) • p j)
    rw [smul_smul]
    have hmul : r * (1 / r) = 1 := by field_simp
    rw [hmul, one_smul]
  have hfeas := radial_replacement_feasible p j r b u hb hr hj hD hu hpi
    hpack (by simpa [r] using hmax')
  have hb0 : 0 ≤ b := by linarith
  have hq : ‖b • u‖ = b := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0, hu]
  exact hno j (b • u) hj hq hfeas

end CP15
