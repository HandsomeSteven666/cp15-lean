import CP15.CyclicInnerModel

namespace CP15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def k10EmptyPattern (p : Fin 16) (i : Fin 5) : ℕ :=
  ![![0, 0, 0, 0, 5], ![1, 0, 0, 0, 4], ![0, 1, 0, 0, 4], ![2, 0, 0, 0, 3], ![1, 1, 0, 0, 3], ![1, 0, 1, 0, 3], ![1, 0, 0, 1, 3], ![0, 2, 0, 0, 3], ![0, 1, 1, 0, 3], ![2, 1, 0, 0, 2], ![2, 0, 1, 0, 2], ![1, 2, 0, 0, 2], ![1, 1, 1, 0, 2], ![1, 1, 0, 1, 2], ![1, 0, 2, 0, 2], ![1, 1, 1, 1, 1]] p i

/-- Every count word is inspected by the kernel. The sum condition leaves
126 words; all sixteen dihedral orbits, including alternation, occur. -/
theorem k10_empty_orbit_checked : ∀ w : Fin 5 → Fin 6,
    (∑ i, (w i).val) = 5 → ∃ p : Fin 16, ∃ a : Fin 5, ∃ reflected : Bool,
      ∀ i, (if reflected then w (a - i - 1) else w (i + a)).val = k10EmptyPattern p i := by
  decide +kernel

theorem CyclicInnerModel.exists_canonical {b : ℝ} {r : Fin 5 → ℝ}
    {e : Fin 5 → ℕ} {g : Fin 5 → ℝ} (h : CyclicInnerModel b r e g) :
    ∃ p : Fin 16, ∃ r' g' : Fin 5 → ℝ, CyclicInnerModel b r' (k10EmptyPattern p) g' := by
  classical
  have he (i : Fin 5) : e i ≤ 5 := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
      Nat.zero_le (e j)) (Finset.mem_univ i)
    simpa only [h.empty_sum] using hh
  let w : Fin 5 → Fin 6 := fun i => ⟨e i, by have hh := he i; omega⟩
  have hw : (∑ i, (w i).val) = 5 := h.empty_sum
  obtain ⟨p, a, reflected, hp⟩ := k10_empty_orbit_checked w hw
  cases reflected
  · have hc := h.rotate a
    have heq : (fun i => e (i + a)) = k10EmptyPattern p := by
      funext i
      simpa [w] using hp i
    rw [heq] at hc
    exact ⟨p, _, _, hc⟩
  · have hc := h.reflect a
    have heq : (fun i => e (a - i - 1)) = k10EmptyPattern p := by
      funext i
      simpa [w] using hp i
    rw [heq] at hc
    exact ⟨p, _, _, hc⟩

end CP15
