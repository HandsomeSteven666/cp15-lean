import CP15.HighRadiusBudget

open scoped InnerProductSpace

namespace CP15

/-- Choose one strict inner blocker and then one actual outer contact for
each nonzero non-outer center in a finite family. If the chosen blockers are
distinct, the exact additive outer-gap budget follows. No injectivity of the
target labels is needed for the selection statement itself. -/
theorem exists_nonOuter_blocker_family_with_conditional_budget
    {ι : Type*} [Fintype ι]
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hFcap : ∀ t, ‖p t‖ < b → ¬TouchesOuter p b t → ‖p t‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ t, ‖p t‖ < b → p t ≠ 0 →
      ∃ j, j ≠ t ∧ dist (p t) (p j) = 2 ∧
        ‖p t‖ ^ 2 < ⟪p j, p t⟫_ℝ)
    (hK : 9 ≤ (boundarySet p b).card)
    (target : ι → Fin 15)
    (htarget : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c) ∧ p (target c) ≠ 0) :
    ∃ (blocker outer : ι → Fin 15),
      (∀ c, blocker c ≠ target c ∧
        dist (p (target c)) (p (blocker c)) = 2 ∧
        ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
        outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
        dist (p (blocker c)) (p (outer c)) = 2 ∧
        ‖p (target c)‖ ^ 2 < ⟪p (blocker c), p (target c)⟫_ℝ) ∧
      (Function.Injective blocker →
        (∑ c : ι, 2 * Real.arccos
          ((b ^ 2 + ‖p (blocker c)‖ ^ 2 - 4) /
            (2 * ‖p (blocker c)‖ * b))) +
          (((boundaryAngles p b).card : ℝ) - (Fintype.card ι : ℝ)) *
            (4 / 7) ≤ 2 * Real.pi) := by
  classical
  let witness (c : ι) := nonOuter_blocker_touches_outer p b hpack
    hFcap hFsmall hblock (target c)
      (htarget c).1 (htarget c).2.1 (htarget c).2.2
  let blocker : ι → Fin 15 := fun c => Classical.choose (witness c)
  have hblocker (c : ι) :
      blocker c ≠ target c ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
      TouchesOuter p b (blocker c) ∧
      ‖p (target c)‖ ^ 2 < ⟪p (blocker c), p (target c)⟫_ℝ :=
    Classical.choose_spec (witness c)
  let outerWitness (c : ι) := (hblocker c).2.2.2.2.1
  let outer : ι → Fin 15 := fun c => Classical.choose (outerWitness c)
  have houter (c : ι) :
      outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
      dist (p (blocker c)) (p (outer c)) = 2 :=
    Classical.choose_spec (outerWitness c)
  refine ⟨blocker, outer, ?_, ?_⟩
  · intro c
    exact ⟨(hblocker c).1, (hblocker c).2.1,
      (hblocker c).2.2.1, (hblocker c).2.2.2.1,
      (houter c).1, (houter c).2.1, (houter c).2.2,
      (hblocker c).2.2.2.2.2⟩
  · intro hinj
    exact large_contact_arccos_card_budget p b hb hbB hpack.2 hD hK
      blocker outer hinj
      (fun c => (hblocker c).2.2.1)
      (fun c => (hblocker c).2.2.2.1.le)
      (fun c => (houter c).2.1)
      (fun c => (houter c).2.2)

end CP15
