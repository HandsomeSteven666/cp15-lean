import CP15.M2K9SharedSixGap

open scoped InnerProductSpace

namespace CP15

/-- The shared-blocker branch, with every high-count, radius-ceiling
and lifted-angle premise discharged from the selected packing. -/
theorem m2_K9_shared_impossible
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hK9 : (boundarySet p b).card = 9)
    (hm2 : (nonOuterIndices p b).card = 2)
    (target blocker outer : Fin 2 → Fin 15)
    (htarget : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧ ¬TouchesOuter p b (target c))
    (hdata : ∀ c, blocker c ≠ target c ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
      outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
      dist (p (blocker c)) (p (outer c)) = 2 ∧
      ‖p (target c)‖ ^ 2 < ⟪p (blocker c), p (target c)⟫_ℝ)
    (hshared : blocker 0 = blocker 1)
    (hqsq : (16 / 3 : ℝ) < ‖p (blocker 0)‖ ^ 2)
    (hbcut : 2 * Real.sqrt 3 < b) : False := by
  have hblock : ‖p (blocker 0)‖ < b ∧
      2 < ‖p (blocker 0)‖ ∧ TouchesOuter p b (blocker 0) :=
    ⟨(hdata 0).2.2.1, (hdata 0).2.2.2.1,
      outer 0, (hdata 0).2.2.2.2.1,
      (hdata 0).2.2.2.2.2.1, (hdata 0).2.2.2.2.2.2.1⟩
  obtain ⟨hhigh, hother⟩ := k9_shared_blocker_high_pair_residual
    p b hb hbB hpack hD hFcap hbcut hK9 hm2 target htarget hno
      (blocker 0) hblock hqsq
  have hanchorT : blocker 0 ∈ touchingInnerSet p b := by
    simpa [touchingInnerSet] using
      (⟨hblock.1, hblock.2.2⟩ :
        ‖p (blocker 0)‖ < b ∧ TouchesOuter p b (blocker 0))
  have hanchorHi : ‖p (blocker 0)‖ ≤ 2385436 / 1000000 :=
    ((hD (blocker 0) hblock.1).trans (D_lt_shared_high_ceiling b hb hbB)).le
  have htouchLow : ∀ k, k ∈ touchingInnerSet p b →
      (29 / 20 : ℝ) ≤ ‖p k‖ := by
    intro k hk
    have hkdata : ‖p k‖ < b ∧ TouchesOuter p b k := by
      simpa [touchingInnerSet] using hk
    exact (touching_radius_gt_29_div_20 p b hbcut k hkdata.2).le
  have hzcontact : dist (p (target 1)) (p (blocker 0)) = 2 := by
    rw [hshared]
    exact (hdata 1).2.1
  have hzblock : ‖p (target 1)‖ ^ 2 <
      ⟪p (blocker 0), p (target 1)⟫_ℝ := by
    rw [hshared]
    exact (hdata 1).2.2.2.2.2.2.2
  exact shared_blocker_actual_impossible p b ‖p (blocker 0)‖
    (blocker 0) (target 0) (target 1) hb hbB hpack hK9 hm2 hD
    (hno 0) (hno 1) (htarget.ne (by decide)) hanchorT rfl hqsq
    hanchorHi (hdata 0).2.1 hzcontact
    (hdata 0).2.2.2.2.2.2.2 hzblock hhigh hother htouchLow hFcap

end CP15
