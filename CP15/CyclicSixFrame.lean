import CP15.M2K9DistinctContactClassification

namespace CP15

set_option maxHeartbeats 0

/-- A lifted cyclic coordinate system. The orientation sign is recorded
explicitly, so reversing a word also reverses the meaning of its two sides.
Only trigonometric differences are fixed; the lifts may cross the usual
polar-argument branch cut. -/
structure LiftedSixFrame (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (orientation : ℝ) : Prop where
  mono : StrictMono φ
  span : φ 5 - φ 0 < 2 * Real.pi
  cosine : ∀ i j,
    Real.cos (polarArg (q i) - polarArg (q j)) = Real.cos (φ i - φ j)
  cross : ∀ i j, orientation * planeCross (q i) (q j) =
    ‖q i‖ * ‖q j‖ * Real.sin (φ j - φ i)

theorem literal_six_frame (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (hmono : StrictMono φ) (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi) :
    LiftedSixFrame q φ 1 := by
  refine ⟨hmono, by linarith, ?_, ?_⟩
  · intro i j
    rw [harg i, harg j]
  · intro i j
    simpa [harg i, harg j] using planeCross_polar (q i) (q j)

private def rotationShift (k i : Fin 6) : ℤ :=
  if (i + k).val < k.val then 1 else 0

private def reversalShift (k i : Fin 6) : ℤ :=
  if k.val < (k - i).val then 1 else 0

noncomputable def rotatedSixLift (φ : Fin 6 → ℝ) (k i : Fin 6) : ℝ :=
  φ (i + k) + (rotationShift k i : ℝ) * (2 * Real.pi)

noncomputable def reversedSixLift (φ : Fin 6 → ℝ) (k i : Fin 6) : ℝ :=
  -φ (k - i) + (reversalShift k i : ℝ) * (2 * Real.pi)

private theorem rotated_six_mono_span (φ : Fin 6 → ℝ)
    (hm : StrictMono φ) (hs : φ 5 - φ 0 < 2 * Real.pi) (k : Fin 6) :
    StrictMono (rotatedSixLift φ k) ∧
      rotatedSixLift φ k 5 - rotatedSixLift φ k 0 < 2 * Real.pi := by
  have h01 := hm (show (0 : Fin 6) < 1 by decide)
  have h12 := hm (show (1 : Fin 6) < 2 by decide)
  have h23 := hm (show (2 : Fin 6) < 3 by decide)
  have h34 := hm (show (3 : Fin 6) < 4 by decide)
  have h45 := hm (show (4 : Fin 6) < 5 by decide)
  constructor
  · intro i j hij
    change i.val < j.val at hij
    fin_cases k <;> fin_cases i <;> fin_cases j
    all_goals try omega
    all_goals norm_num [rotatedSixLift, rotationShift]
    all_goals linarith
  · fin_cases k <;> norm_num [rotatedSixLift, rotationShift] <;> linarith

private theorem reversed_six_mono_span (φ : Fin 6 → ℝ)
    (hm : StrictMono φ) (hs : φ 5 - φ 0 < 2 * Real.pi) (k : Fin 6) :
    StrictMono (reversedSixLift φ k) ∧
      reversedSixLift φ k 5 - reversedSixLift φ k 0 < 2 * Real.pi := by
  have h01 := hm (show (0 : Fin 6) < 1 by decide)
  have h12 := hm (show (1 : Fin 6) < 2 by decide)
  have h23 := hm (show (2 : Fin 6) < 3 by decide)
  have h34 := hm (show (3 : Fin 6) < 4 by decide)
  have h45 := hm (show (4 : Fin 6) < 5 by decide)
  constructor
  · intro i j hij
    change i.val < j.val at hij
    fin_cases k <;> fin_cases i <;> fin_cases j
    all_goals try omega
    all_goals simp only [reversedSixLift, reversalShift, Fin.sub_def]
    all_goals norm_num
    all_goals linarith
  · fin_cases k <;> simp only [reversedSixLift, reversalShift, Fin.sub_def] <;>
      norm_num <;> linarith

theorem LiftedSixFrame.rotate {q : Fin 6 → Plane} {φ : Fin 6 → ℝ}
    {ε : ℝ} (h : LiftedSixFrame q φ ε) (k : Fin 6) :
    LiftedSixFrame (fun i => q (i + k)) (rotatedSixLift φ k) ε := by
  obtain ⟨hm, hs⟩ := rotated_six_mono_span φ h.mono h.span k
  refine ⟨hm, hs, ?_, ?_⟩
  · intro i j
    rw [h.cosine]
    have heq : rotatedSixLift φ k i - rotatedSixLift φ k j =
        (φ (i + k) - φ (j + k)) +
          ((rotationShift k i - rotationShift k j : ℤ) : ℝ) *
            (2 * Real.pi) := by
      simp only [rotatedSixLift, Int.cast_sub]
      ring
    rw [heq, Real.cos_add_int_mul_two_pi]
  · intro i j
    rw [h.cross]
    have heq : rotatedSixLift φ k j - rotatedSixLift φ k i =
        (φ (j + k) - φ (i + k)) +
          ((rotationShift k j - rotationShift k i : ℤ) : ℝ) *
            (2 * Real.pi) := by
      simp only [rotatedSixLift, Int.cast_sub]
      ring
    rw [heq, Real.sin_add_int_mul_two_pi]

theorem LiftedSixFrame.reverse {q : Fin 6 → Plane} {φ : Fin 6 → ℝ}
    {ε : ℝ} (h : LiftedSixFrame q φ ε) (k : Fin 6) :
    LiftedSixFrame (fun i => q (k - i)) (reversedSixLift φ k) (-ε) := by
  obtain ⟨hm, hs⟩ := reversed_six_mono_span φ h.mono h.span k
  refine ⟨hm, hs, ?_, ?_⟩
  · intro i j
    rw [h.cosine]
    have heq : reversedSixLift φ k i - reversedSixLift φ k j =
        -(φ (k - i) - φ (k - j)) +
          ((reversalShift k i - reversalShift k j : ℤ) : ℝ) *
            (2 * Real.pi) := by
      simp only [reversedSixLift, Int.cast_sub]
      ring
    rw [heq, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  · intro i j
    rw [neg_mul, h.cross]
    have heq : reversedSixLift φ k j - reversedSixLift φ k i =
        -(φ (k - j) - φ (k - i)) +
          ((reversalShift k j - reversalShift k i : ℤ) : ℝ) *
            (2 * Real.pi) := by
      simp only [reversedSixLift, Int.cast_sub]
      ring
    rw [heq, Real.sin_add_int_mul_two_pi, Real.sin_neg]
    ring

/-- A dihedral word reduction now gives actual lifted geometry. A cyclic
shift never assumes that the principal polar arguments remain sorted. -/
theorem dihedral_word_actual_lift
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ) (w : Fin 6 → M2Kind)
    (hframe : LiftedSixFrame q φ 1)
    (horbit : dihedralEquivalent w wordAHAHLL) :
    ∃ f : Fin 6 → Fin 6, ∃ ψ : Fin 6 → ℝ, ∃ ε : ℝ,
      Function.Bijective f ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ i, w (f i) = wordAHAHLL i) ∧
      LiftedSixFrame (fun i => q (f i)) ψ ε ∧
      ((∀ i, f (i + 1) = f i + 1) ∨ (∀ i, f (i + 1) + 1 = f i)) := by
  rcases horbit with ⟨k, hf | hr⟩
  · let a : Fin 6 := 0 - k
    let f : Fin 6 → Fin 6 := fun i => i + a
    have hinj : Function.Injective f := by
      intro i j hij
      simp only [f, a, Fin.sub_def, Fin.add_def] at hij
      fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num at *
    refine ⟨f, rotatedSixLift φ a, 1,
      ⟨hinj, Finite.surjective_of_injective hinj⟩, Or.inl rfl, ?_,
      hframe.rotate a, Or.inl ?_⟩
    · intro i
      rw [hf]
      congr 1
      dsimp [f, a]
      fin_cases i <;> fin_cases k <;> decide
    · intro i
      dsimp [f, a]
      fin_cases i <;> fin_cases k <;> decide
  · let f : Fin 6 → Fin 6 := fun i => k - i
    have hinj : Function.Injective f := by
      intro i j hij
      simp only [f, Fin.sub_def] at hij
      fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num at *
    refine ⟨f, reversedSixLift φ k, -1,
      ⟨hinj, Finite.surjective_of_injective hinj⟩, Or.inr rfl, ?_,
      hframe.reverse k, Or.inr ?_⟩
    · intro i
      rw [hr]
      congr 1
      dsimp [f]
      fin_cases i <;> fin_cases k <;> decide
    · intro i
      dsimp [f]
      fin_cases i <;> fin_cases k <;> decide

end CP15
