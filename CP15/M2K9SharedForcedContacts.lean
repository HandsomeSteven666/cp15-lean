import CP15.M2K9SharedHighCeiling
import CP15.M2TangentialSelection

open scoped InnerProductSpace

namespace CP15

/-- The cross product of two vectors, resolved into their components
parallel and perpendicular to a nonzero reference vector. -/
theorem planeCross_resolve (y x z : Plane) :
    ‖y‖ ^ 2 * planeCross x z =
      ⟪y, x⟫_ℝ * planeCross y z -
        ⟪y, z⟫_ℝ * planeCross y x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [planeCross, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- At either target of a strict shared blocker, the other target
lies on the same open tangential side as the blocker. -/
theorem strict_shared_target_other_same_cross_side
    (x z y : Plane)
    (hy : ‖y‖ < 12 / 5)
    (hxy : dist x y = 2) (hzy : dist z y = 2)
    (hblockx : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hblockz : ‖z‖ ^ 2 < ⟪y, z⟫_ℝ)
    (hxz : 2 ≤ dist x z) :
    0 < planeCross x (y - x) * planeCross x (z - x) := by
  have hcross := strict_shared_contacts_cross_negative x z y hy
    hxy hzy hblockx hblockz hxz
  have hresolve := planeCross_resolve y x z
  have hxycross : planeCross x (y - x) = -planeCross y x := by
    simp [planeCross, PiLp.sub_apply]
    ring
  have hxzcross : planeCross x (z - x) = planeCross x z := by
    simp [planeCross, PiLp.sub_apply]
    ring
  rw [hxycross, hxzcross]
  have hxpos : 0 < ⟪y, x⟫_ℝ := by
    nlinarith [sq_nonneg ‖x‖]
  have hzpos : 0 < ⟪y, z⟫_ℝ := by
    nlinarith [sq_nonneg ‖z‖]
  have hypos : 0 < ‖y‖ ^ 2 := by
    have hnonzero : y ≠ 0 := by
      intro hzero
      simp [hzero] at hblockx
      nlinarith [sq_nonneg ‖x‖]
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hnonzero
    positivity
  have hnegprod :
      0 < -(⟪y, x⟫_ℝ *
        (planeCross y x * planeCross y z)) := by
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hxpos hcross)
  have hposprod :
      0 ≤ ⟪y, z⟫_ℝ * planeCross y x ^ 2 := by positivity
  have hR : 0 < ‖y‖ ^ 2 *
      (-planeCross y x * planeCross x z) := by
    calc
      ‖y‖ ^ 2 * (-planeCross y x * planeCross x z) =
          -planeCross y x * (‖y‖ ^ 2 * planeCross x z) := by ring
      _ = -(⟪y, x⟫_ℝ *
          (planeCross y x * planeCross y z)) +
            ⟪y, z⟫_ℝ * planeCross y x ^ 2 := by
        rw [hresolve]
        ring
      _ > 0 := by linarith
  by_contra hnot
  have hle : -planeCross y x * planeCross x z ≤ 0 :=
    le_of_not_gt hnot
  exact (not_lt_of_ge
    (mul_nonpos_of_nonneg_of_nonpos hypos.le hle)) hR

/-- With exactly two non-outer centers, every non-outer index is one of
the selected pair. -/
private theorem m2_nonouter_index_eq_pair
    (p : Fin 15 → Plane) (b : ℝ)
    (hm2 : (nonOuterIndices p b).card = 2)
    (x z : Fin 15) (hxz : x ≠ z)
    (hx : ‖p x‖ < b ∧ ¬TouchesOuter p b x)
    (hz : ‖p z‖ < b ∧ ¬TouchesOuter p b z)
    (j : Fin 15) (hj : j ∈ nonOuterIndices p b) :
    j = x ∨ j = z := by
  classical
  by_contra hnot
  have hjx : j ≠ x := fun h => hnot (Or.inl h)
  have hjz : j ≠ z := fun h => hnot (Or.inr h)
  have hsub : ({x, z, j} : Finset (Fin 15)) ⊆
      nonOuterIndices p b := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · simpa [nonOuterIndices] using hx
    · simpa [nonOuterIndices] using hz
    · exact hj
  have hc := Finset.card_le_card hsub
  have hcard3 : ({x, z, j} : Finset (Fin 15)).card = 3 := by
    simp [hxz, hjx, hjz, hxz.symm, hjx.symm, hjz.symm]
  omega

/-- In the selected shared-blocker branch, each non-outer center has
an active contact with a touching inner center on the angular side
opposite the common blocker. This is the first forced-contact fact;
it does not identify which touching inner center is first cyclically. -/
theorem k9_shared_target_forced_touching_contact
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hm2 : (nonOuterIndices p b).card = 2)
    (x z y : Fin 15) (hxz : x ≠ z)
    (hx : ‖p x‖ < b ∧ ¬TouchesOuter p b x)
    (hz : ‖p z‖ < b ∧ ¬TouchesOuter p b z)
    (hy : ‖p y‖ < b)
    (hxy : dist (p x) (p y) = 2)
    (hzy : dist (p z) (p y) = 2)
    (hblockx : ‖p x‖ ^ 2 < ⟪p y, p x⟫_ℝ)
    (hblockz : ‖p z‖ ^ 2 < ⟪p y, p z⟫_ℝ) :
    ∃ j ∈ touchingInnerSet p b,
      j ≠ y ∧ j ≠ z ∧
      dist (p x) (p j) = 2 ∧
      planeCross (p x) (p y - p x) *
        planeCross (p x) (p j - p x) < 0 := by
  have hyhi : ‖p y‖ < 12 / 5 :=
    (hD y hy).trans
      (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)
  have hsame := strict_shared_target_other_same_cross_side
    (p x) (p z) (p y) hyhi hxy hzy hblockx hblockz
    (hpack.2 x z hxz)
  have htwo := m2_nonOuter_two_sided_contacts p b hb hbB hpack
    hK hS hD hFcap x z hxz hx hz
  let a := planeCross (p x) (p y - p x)
  obtain ⟨j, hjx, hjcontact, hjopposite⟩ :
      ∃ j, j ≠ x ∧ dist (p x) (p j) = 2 ∧
        a * planeCross (p x) (p j - p x) < 0 := by
    by_cases ha : 0 < a
    · obtain ⟨j, hjx, hjc, hjneg⟩ := htwo.2
      exact ⟨j, hjx, hjc, mul_neg_of_pos_of_neg ha hjneg⟩
    · have ha' : a < 0 := by
        dsimp [a] at ha
        have hne : a ≠ 0 := by
          intro hzero
          dsimp [a] at hzero
          rw [hzero] at hsame
          norm_num at hsame
        exact lt_of_le_of_ne (le_of_not_gt ha) hne
      obtain ⟨j, hjx, hjc, hjpos⟩ := htwo.1
      exact ⟨j, hjx, hjc, mul_neg_of_neg_of_pos ha' hjpos⟩
  have hjy : j ≠ y := by
    intro heq
    subst j
    dsimp [a] at hjopposite
    nlinarith [sq_nonneg (planeCross (p x) (p y - p x))]
  have hjz : j ≠ z := by
    intro heq
    subst j
    have hs : 0 ≤ a * planeCross (p x) (p z - p x) := by
      simpa [a] using hsame.le
    exact (not_lt_of_ge hs) hjopposite
  have hjinner : ‖p j‖ < b := by
    by_contra hnot
    have hjbd : ‖p j‖ = b :=
      le_antisymm (hpack.1 j) (le_of_not_gt hnot)
    exact hx.2 ⟨j, hjx, hjbd, hjcontact⟩
  have hjtouch : TouchesOuter p b j := by
    by_contra hnot
    have hjM : j ∈ nonOuterIndices p b := by
      simpa [nonOuterIndices] using
        (⟨hjinner, hnot⟩ : ‖p j‖ < b ∧ ¬TouchesOuter p b j)
    rcases m2_nonouter_index_eq_pair p b hm2 x z hxz hx hz j hjM with
      rfl | rfl
    · exact hjx rfl
    · exact hjz rfl
  exact ⟨j, by simpa [touchingInnerSet] using
    (⟨hjinner, hjtouch⟩ : ‖p j‖ < b ∧ TouchesOuter p b j),
    hjy, hjz, hjcontact, hjopposite⟩

end CP15
