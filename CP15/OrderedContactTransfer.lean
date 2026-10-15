import CP15.TangentialSupport

open scoped InnerProductSpace

namespace CP15

/-- An actual contact of a non-outer-touching center is strictly inner.
This discharges the premise needed to use a complete inner-center list. -/
theorem contact_of_nonOuter_is_inner
    {n : ℕ} (p : Fin n → Plane) (b : ℝ) (hpack : InDisk b p)
    (i j : Fin n) (hno : ¬TouchesOuter p b i)
    (hji : j ≠ i) (hc : dist (p i) (p j) = 2) : ‖p j‖ < b := by
  by_contra hnot
  have hboundary : ‖p j‖ = b := le_antisymm (hpack j) (le_of_not_gt hnot)
  exact hno ⟨j, hji, hboundary, hc⟩

/-- Transfer all two-sided contacts, including contacts other than the
selected blocker, through an actual complete index map. An arbitrary
six-center geometric model without this map cannot justify the conclusion. -/
theorem two_sided_contacts_in_complete_inner_order
    {n k : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (htwo : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        0 < planeCross (p i) (p j - p i)) ∧
      (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        planeCross (p i) (p j - p i) < 0))
    (q : Fin k → Plane) (ix : Fin k → Fin n)
    (hindex : ∀ i, q i = p (ix i))
    (hinner : ∀ i, ‖p (ix i)‖ < b)
    (hcover : ∀ j, ‖p j‖ < b → ∃ i, ix i = j)
    (i : Fin k) (hno : ¬TouchesOuter p b (ix i)) (hx : q i ≠ 0) :
    (∃ j, j ≠ i ∧ dist (q i) (q j) = 2 ∧
      0 < planeCross (q i) (q j - q i)) ∧
    (∃ j, j ≠ i ∧ dist (q i) (q j) = 2 ∧
      planeCross (q i) (q j - q i) < 0) := by
  have hx' : p (ix i) ≠ 0 := by simpa [hindex i] using hx
  obtain ⟨hpos, hneg⟩ := htwo (ix i) (hinner i) hx'
  have htransfer (j : Fin n) (hji : j ≠ ix i)
      (hc : dist (p (ix i)) (p j) = 2) :
      ∃ r : Fin k, r ≠ i ∧ ix r = j := by
    have hjinner := contact_of_nonOuter_is_inner p b hpack.1 (ix i) j hno hji hc
    obtain ⟨r, hr⟩ := hcover j hjinner
    have hri : r ≠ i := by
      intro h
      subst r
      exact hji hr.symm
    exact ⟨r, hri, hr⟩
  constructor
  · obtain ⟨j, hji, hc, hcross⟩ := hpos
    obtain ⟨r, hri, hr⟩ := htransfer j hji hc
    refine ⟨r, hri, ?_, ?_⟩
    · simpa [hindex i, hindex r, hr] using hc
    · simpa [hindex i, hindex r, hr] using hcross
  · obtain ⟨j, hji, hc, hcross⟩ := hneg
    obtain ⟨r, hri, hr⟩ := htransfer j hji hc
    refine ⟨r, hri, ?_, ?_⟩
    · simpa [hindex i, hindex r, hr] using hc
    · simpa [hindex i, hindex r, hr] using hcross

end CP15
