import CP15.WeakPolarOrder

namespace CP15

/-- Lift to the full turn beginning at a specified actual polar argument.
The comparison is strict, so ties stay at the beginning of the turn. -/
noncomputable def polarLiftFrom (a : ℝ) (q : Plane) : ℝ := by
  classical
  exact if polarArg q < a then polarArg q + 2 * Real.pi else polarArg q

theorem polarLiftFrom_bounds (a : ℝ) (ha : -Real.pi < a ∧ a ≤ Real.pi) (q : Plane) :
    a ≤ polarLiftFrom a q ∧ polarLiftFrom a q ≤ a + 2 * Real.pi := by
  classical
  have hq := polarArg_range q
  by_cases hqa : polarArg q < a
  · simp only [polarLiftFrom, if_pos hqa]
    constructor <;> linarith
  · simp only [polarLiftFrom, if_neg hqa]
    constructor <;> linarith

theorem polarLiftFrom_self (q : Plane) : polarLiftFrom (polarArg q) q = polarArg q := by
  simp [polarLiftFrom]

theorem polarLiftFrom_cos (a : ℝ) (x y : Plane) :
    Real.cos (polarArg x - polarArg y) =
      Real.cos (polarLiftFrom a x - polarLiftFrom a y) := by
  classical
  by_cases hx : polarArg x < a <;> by_cases hy : polarArg y < a
  · simp only [polarLiftFrom, if_pos hx, if_pos hy]
    congr 1
    ring
  · simp only [polarLiftFrom, if_pos hx, if_neg hy]
    rw [show polarArg x + 2 * Real.pi - polarArg y =
      (polarArg x - polarArg y) + 2 * Real.pi by ring, Real.cos_add_two_pi]
  · simp only [polarLiftFrom, if_neg hx, if_pos hy]
    rw [show polarArg x - (polarArg y + 2 * Real.pi) =
      (polarArg x - polarArg y) - 2 * Real.pi by ring, Real.cos_sub_two_pi]
  · simp only [polarLiftFrom, if_neg hx, if_neg hy]

/-- A bijective weak order of every supplied center in the specified
turn. No angular injectivity is assumed and no tied center is discarded. -/
theorem exists_relative_polar_permutation {n : ℕ} (q : Fin n → Plane)
    (a : ℝ) (ha : -Real.pi < a ∧ a ≤ Real.pi) :
    ∃ src : Equiv.Perm (Fin n), ∃ φ : Fin n → ℝ,
      Monotone φ ∧ (∀ i, polarLiftFrom a (q (src i)) = φ i) ∧
      (∀ i, a ≤ φ i ∧ φ i ≤ a + 2 * Real.pi) := by
  classical
  let src := Tuple.sort (fun i => polarLiftFrom a (q i))
  let φ : Fin n → ℝ := fun i => polarLiftFrom a (q (src i))
  refine ⟨src, φ, ?_, fun _ => rfl, ?_⟩
  · exact Tuple.monotone_sort (fun i => polarLiftFrom a (q i))
  · intro i
    exact polarLiftFrom_bounds a ha (q (src i))

end CP15
