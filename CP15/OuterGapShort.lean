import CP15.OuterCountBound

namespace CP15

/-- With at least nine boundary points, the closing polar gap is shorter
than `π`. This is an actual packing theorem, not a gap-list hypothesis. -/
theorem ordered_boundary_wrap_gap_lt_pi (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 9 ≤ (boundarySet p b).card) :
    (boundaryAngles p b).orderEmbOfFin rfl ⟨0, by
      rw [boundaryAngles_card p b hsep]; omega⟩ +
      2 * Real.pi -
      (boundaryAngles p b).orderEmbOfFin rfl
        ⟨(boundaryAngles p b).card - 1, by
          rw [boundaryAngles_card p b hsep]; omega⟩ < Real.pi := by
  let s := boundaryAngles p b
  have hsK : 9 ≤ s.card := by rw [boundaryAngles_card p b hsep]; exact hK
  let e := s.orderEmbOfFin rfl
  let first : Fin s.card := ⟨0, by omega⟩
  let last : Fin s.card := ⟨s.card - 1, by omega⟩
  let f : ℕ → ℝ := fun n => if hn : n < s.card then e ⟨n, hn⟩ else e last
  have hstep (n : ℕ) (hn : n ∈ Finset.range (s.card - 1)) :
      (4 / 7 : ℝ) ≤ f (n + 1) - f n := by
    have hn0 : n < s.card := by simp at hn; omega
    have hn1 : n + 1 < s.card := by simp at hn; omega
    have hlt : (⟨n, hn0⟩ : Fin s.card) < ⟨n + 1, hn1⟩ := by
      change n < n + 1
      omega
    have hgap := ordered_boundary_angle_gap_ge_four_sevenths p b hb hbB hsep
      ⟨n, hn0⟩ ⟨n + 1, hn1⟩ hlt
    simpa [f, hn0, hn1, s, e] using hgap
  have hsum : ((s.card - 1 : ℕ) : ℝ) * (4 / 7 : ℝ) ≤
      f (s.card - 1) - f 0 := by
    have h := Finset.sum_le_sum
      (s := Finset.range (s.card - 1)) (fun n hn => hstep n hn)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    rw [Finset.sum_range_sub] at h
    simpa using h
  have hf0 : f 0 = e first := by
    have hz : 0 < s.card := by omega
    simp [f, first, hz]
  have hflast : f (s.card - 1) = e last := by
    simp [f, last, Nat.sub_lt (by omega : 0 < s.card) (by omega : 0 < 1)]
  have hcast : (8 : ℝ) ≤ (s.card - 1 : ℕ) := by exact_mod_cast (by omega : 8 ≤ s.card - 1)
  have hpi : Real.pi < (32 / 7 : ℝ) := by linarith [Real.pi_lt_d20]
  have hfinal : e first + 2 * Real.pi - e last < Real.pi := by
    rw [hf0, hflast] at hsum
    nlinarith
  simpa [s, e, first, last] using hfinal

/-- Every ordinary consecutive gap is also shorter than `π`. The proof
erases that step from the telescoping sum, so all other gaps remain counted. -/
theorem ordered_boundary_adjacent_gap_lt_pi (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 9 ≤ (boundarySet p b).card)
    (i : Fin (boundaryAngles p b).card)
    (hi : i.val + 1 < (boundaryAngles p b).card) :
    (boundaryAngles p b).orderEmbOfFin rfl ⟨i.val + 1, hi⟩ -
      (boundaryAngles p b).orderEmbOfFin rfl i < Real.pi := by
  let s := boundaryAngles p b
  have hsK : 9 ≤ s.card := by rw [boundaryAngles_card p b hsep]; exact hK
  let e := s.orderEmbOfFin rfl
  let first : Fin s.card := ⟨0, by omega⟩
  let last : Fin s.card := ⟨s.card - 1, by omega⟩
  let f : ℕ → ℝ := fun n => if hn : n < s.card then e ⟨n, hn⟩ else e last
  let t := Finset.range (s.card - 1)
  have hstep (n : ℕ) (hn : n ∈ t) :
      (4 / 7 : ℝ) ≤ f (n + 1) - f n := by
    have hn0 : n < s.card := by simp [t] at hn; omega
    have hn1 : n + 1 < s.card := by simp [t] at hn; omega
    have hlt : (⟨n, hn0⟩ : Fin s.card) < ⟨n + 1, hn1⟩ := by
      change n < n + 1
      omega
    have hgap := ordered_boundary_angle_gap_ge_four_sevenths p b hb hbB hsep
      ⟨n, hn0⟩ ⟨n + 1, hn1⟩ hlt
    simpa [f, hn0, hn1, s, e] using hgap
  have himem : i.val ∈ t := by
    have hi' : i.val + 1 < s.card := hi
    simp [t]
    omega
  have hother : ((s.card - 2 : ℕ) : ℝ) * (4 / 7 : ℝ) ≤
      ∑ n ∈ t.erase i.val, (f (n + 1) - f n) := by
    have h := Finset.sum_le_sum (s := t.erase i.val)
      (fun n hn => hstep n (Finset.mem_of_mem_erase hn))
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    have hcard : (t.erase i.val).card = s.card - 2 := by
      rw [Finset.card_erase_of_mem himem]
      simp [t]
      omega
    simpa [hcard] using h
  have hdecomp : (∑ n ∈ t.erase i.val, (f (n + 1) - f n)) +
      (f (i.val + 1) - f i.val) = f (s.card - 1) - f 0 := by
    have h := Finset.sum_erase_add t (fun n => f (n + 1) - f n) himem
    rw [Finset.sum_range_sub] at h
    exact h
  have hwrap := ordered_boundary_wrap_gap_ge_four_sevenths p b hb hbB hsep
    (by rw [boundaryAngles_card p b hsep]; omega)
  have hf0 : f 0 = e first := by
    have hz : 0 < s.card := by omega
    simp [f, first, hz]
  have hflast : f (s.card - 1) = e last := by
    simp [f, last, Nat.sub_lt (by omega : 0 < s.card) (by omega : 0 < 1)]
  have hwrap' : (4 / 7 : ℝ) ≤ f 0 + 2 * Real.pi - f (s.card - 1) := by
    simpa [s, e, hf0, hflast, first, last] using hwrap
  have hcast : (7 : ℝ) ≤ (s.card - 2 : ℕ) := by exact_mod_cast (by omega : 7 ≤ s.card - 2)
  have hpi : Real.pi < (32 / 7 : ℝ) := by linarith [Real.pi_lt_d20]
  have hgoal : f (i.val + 1) - f i.val < Real.pi := by
    nlinarith
  have hii : i.val < s.card := i.isLt
  simpa [f, hii, hi, s, e] using hgoal

end CP15
