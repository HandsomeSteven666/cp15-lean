import CP15.CyclicAngles

namespace CP15

/-- Sort the indices themselves. Coincident polar arguments remain
distinct centers and are retained in a nondecreasing angular order. -/
theorem exists_weakly_sorted_polar_permutation {n : ℕ} (q : Fin n → Plane) :
    ∃ src : Equiv.Perm (Fin n), ∃ φ : Fin n → ℝ,
      Monotone φ ∧ (∀ i, polarArg (q (src i)) = φ i) ∧
      (∀ i, -Real.pi < φ i ∧ φ i ≤ Real.pi) := by
  classical
  let src := Tuple.sort (fun i => polarArg (q i))
  let φ : Fin n → ℝ := fun i => polarArg (q (src i))
  refine ⟨src, φ, ?_, fun _ => rfl, ?_⟩
  · exact Tuple.monotone_sort (fun i => polarArg (q i))
  · intro i
    exact polarArg_range (q (src i))

theorem cyclicAngleGap_nonneg_of_monotone {n : ℕ} (φ : Fin (n + 1) → ℝ)
    (hmono : Monotone φ) (hrange : ∀ i, -Real.pi < φ i ∧ φ i ≤ Real.pi)
    (i : Fin (n + 1)) : 0 ≤ cyclicAngleGap φ i := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [cyclicAngleGap, ite_true, Fin.last_add_one]
    linarith [(hrange 0).1, (hrange (Fin.last n)).2]
  · have hiLt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
    have hsucc : i < i + 1 := by
      change i.val < (i + 1).val
      rw [Fin.val_add_one_of_lt hiLt]
      omega
    simp only [cyclicAngleGap, if_neg hi, add_zero]
    exact sub_nonneg.mpr (hmono hsucc.le)

end CP15
