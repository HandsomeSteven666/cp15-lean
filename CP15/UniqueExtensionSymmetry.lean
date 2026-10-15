import CP15.GlobalUniquenessLogic

namespace CP15

/-- Congruence relevant to a disk centered at the origin: an orthogonal
linear map, including reflections, followed by relabeling. -/
def CenteredCongruent15 (q r : Fin 15 → Plane) : Prop :=
  ∃ σ : Fin 15 ≃ Fin 15, ∃ T : Plane ≃ₗᵢ[ℝ] Plane,
    ∀ i, q i = T (r (σ i))

theorem uniquePointFromOthers_of_centeredCongruent
    (q r : Fin 15 → Plane) (b : ℝ)
    (hqr : CenteredCongruent15 q r)
    (hr : UniquePointFromOthers r b) :
    UniquePointFromOthers q b := by
  obtain ⟨σ, T, hq⟩ := hqr
  intro i x hx hdist
  have hxs : ‖T.symm x‖ ≤ b := by
    simpa using hx
  have hother : ∀ k, k ≠ σ i → 2 ≤ dist (T.symm x) (r k) := by
    intro k hk
    let j := σ.symm k
    have hji : j ≠ i := by
      intro heq
      have hkeq : k = σ i := by
        simpa [j, heq] using (σ.apply_symm_apply k).symm
      exact hk hkeq
    have h := hdist j hji
    have hqj : q j = T (r k) := by
      simpa [j] using hq j
    rw [hqj] at h
    have hd : dist (T.symm x) (r k) = dist x (T (r k)) := by
      have hh := T.dist_map (T.symm x) (r k)
      simpa using hh.symm
    simpa [hd] using h
  have heq := hr (σ i) (T.symm x) hxs hother
  have hxeq := congrArg T heq
  simpa [hq i] using hxeq

theorem uniqueOnePointExtension_of_centeredCongruent
    (q r : Fin 15 → Plane) (b : ℝ)
    (hqr : CenteredCongruent15 q r)
    (hr : UniquePointFromOthers r b) :
    UniqueOnePointExtension q b :=
  uniqueOnePointExtension_of_uniquePointFromOthers q b
    (uniquePointFromOthers_of_centeredCongruent q r b hqr hr)

theorem uniqueBoundaryPointFromOthers_of_centeredCongruent
    (q r : Fin 15 → Plane) (b : ℝ)
    (hqr : CenteredCongruent15 q r)
    (hr : UniqueBoundaryPointFromOthers r b) :
    UniqueBoundaryPointFromOthers q b := by
  obtain ⟨σ, T, hq⟩ := hqr
  intro i hi x hx hdist
  have hri : ‖r (σ i)‖ = b := by
    simpa [hq i] using hi
  have hxs : ‖T.symm x‖ ≤ b := by
    simpa using hx
  have hother : ∀ k, k ≠ σ i → 2 ≤ dist (T.symm x) (r k) := by
    intro k hk
    let j := σ.symm k
    have hji : j ≠ i := by
      intro heq
      have hkeq : k = σ i := by
        simpa [j, heq] using (σ.apply_symm_apply k).symm
      exact hk hkeq
    have h := hdist j hji
    have hqj : q j = T (r k) := by
      simpa [j] using hq j
    rw [hqj] at h
    have hd : dist (T.symm x) (r k) = dist x (T (r k)) := by
      have hh := T.dist_map (T.symm x) (r k)
      simpa using hh.symm
    simpa [hd] using h
  have heq := hr (σ i) hri (T.symm x) hxs hother
  have hxeq := congrArg T heq
  simpa [hq i] using hxeq

end CP15
