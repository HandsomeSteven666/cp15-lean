import CP15.ChordAngleBound
import CP15.NonOuterStructure

namespace CP15

/-- Summing the ordinary and closing angular gaps gives the universal
perimeter inequality `2K/b ≤ 2π`. This uses only actual boundary centers. -/
theorem boundary_count_perimeter_bound (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hsep : Separated p 2)
    (hK : 2 ≤ (boundarySet p b).card) :
    ((boundarySet p b).card : ℝ) * (2 / b) ≤ 2 * Real.pi := by
  let s := boundaryAngles p b
  have hsK : 2 ≤ s.card := by rw [boundaryAngles_card p b hsep]; exact hK
  let e := s.orderEmbOfFin rfl
  let first : Fin s.card := ⟨0, by omega⟩
  let last : Fin s.card := ⟨s.card - 1, by omega⟩
  let f : ℕ → ℝ := fun n => if hn : n < s.card then e ⟨n, hn⟩ else e last
  have hstep (n : ℕ) (hn : n ∈ Finset.range (s.card - 1)) :
      2 / b ≤ f (n + 1) - f n := by
    have hn0 : n < s.card := by simp at hn; omega
    have hn1 : n + 1 < s.card := by simp at hn; omega
    have hlt : (⟨n, hn0⟩ : Fin s.card) < ⟨n + 1, hn1⟩ := by
      change n < n + 1
      omega
    have hgap := ordered_boundary_angle_gap_ge_two_div p b hb hsep
      ⟨n, hn0⟩
      ⟨n + 1, hn1⟩
      (by exact hlt)
    simpa [f, hn0, hn1, s, e] using hgap
  have hsum : ((s.card - 1 : ℕ) : ℝ) * (2 / b) ≤
      f (s.card - 1) - f 0 := by
    have h := Finset.sum_le_sum
      (s := Finset.range (s.card - 1))
      (fun n hn => hstep n hn)
    simp only [Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at h
    rw [Finset.sum_range_sub] at h
    simpa using h
  have hwrap := ordered_boundary_wrap_gap_ge_two_div p b hb hsep hsK
  have hf0 : f 0 = e first := by
    have hz : 0 < s.card := by omega
    simp [f, first, hz]
  have hflast : f (s.card - 1) = e last := by
    simp [f, last, Nat.sub_lt (by omega : 0 < s.card) (by omega : 0 < 1)]
  have hwrap' : 2 / b ≤ f 0 + 2 * Real.pi - f (s.card - 1) := by
    simpa [s, e, hf0, hflast, first, last] using hwrap
  have hnat : ((s.card - 1 : ℕ) : ℝ) + 1 = s.card := by
    have : 0 < s.card := by omega
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ s.card)
  have hpos : 0 ≤ 2 / b := by positivity
  have hs : ((s.card : ℝ) * (2 / b)) ≤ 2 * Real.pi := by
    nlinarith
  simpa [s, boundaryAngles_card p b hsep] using hs

/-- Abstract telescoping form for any established gap lower bound. -/
theorem boundary_count_perimeter_bound_of_gaps (p : Fin 15 → Plane) (b α : ℝ)
    (hsep : Separated p 2) (hK : 2 ≤ (boundarySet p b).card)
    (hsK : 2 ≤ (boundaryAngles p b).card)
    (hstep : ∀ i j : Fin (boundaryAngles p b).card, i < j →
      α ≤ (boundaryAngles p b).orderEmbOfFin rfl j -
        (boundaryAngles p b).orderEmbOfFin rfl i)
    (hwrap : α ≤
      (boundaryAngles p b).orderEmbOfFin rfl ⟨0, by omega⟩ +
        2 * Real.pi -
        (boundaryAngles p b).orderEmbOfFin rfl
          ⟨(boundaryAngles p b).card - 1, by omega⟩) :
    ((boundarySet p b).card : ℝ) * α ≤ 2 * Real.pi := by
  let s := boundaryAngles p b
  have hsK' : 2 ≤ s.card := hsK
  let e := s.orderEmbOfFin rfl
  let first : Fin s.card := ⟨0, by omega⟩
  let last : Fin s.card := ⟨s.card - 1, by omega⟩
  let f : ℕ → ℝ := fun n => if hn : n < s.card then e ⟨n, hn⟩ else e last
  have hstep' (n : ℕ) (hn : n ∈ Finset.range (s.card - 1)) :
      α ≤ f (n + 1) - f n := by
    have hn0 : n < s.card := by simp at hn; omega
    have hn1 : n + 1 < s.card := by simp at hn; omega
    have hlt : (⟨n, hn0⟩ : Fin s.card) < ⟨n + 1, hn1⟩ := by
      change n < n + 1
      omega
    have hgap := hstep ⟨n, hn0⟩ ⟨n + 1, hn1⟩ hlt
    simpa [f, hn0, hn1, s, e] using hgap
  have hsum : ((s.card - 1 : ℕ) : ℝ) * α ≤
      f (s.card - 1) - f 0 := by
    have h := Finset.sum_le_sum
      (s := Finset.range (s.card - 1))
      (fun n hn => hstep' n hn)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    rw [Finset.sum_range_sub] at h
    simpa using h
  have hf0 : f 0 = e first := by
    have hz : 0 < s.card := by omega
    simp [f, first, hz]
  have hflast : f (s.card - 1) = e last := by
    simp [f, last, Nat.sub_lt (by omega : 0 < s.card) (by omega : 0 < 1)]
  have hwrap' : α ≤ f 0 + 2 * Real.pi - f (s.card - 1) := by
    simpa [s, e, hf0, hflast, first, last] using hwrap
  have hnat : ((s.card - 1 : ℕ) : ℝ) + 1 = s.card := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ s.card)
  have hmul := congrArg (fun t : ℝ => t * α) hnat
  have hs : ((s.card : ℝ) * α) ≤ 2 * Real.pi := by
    nlinarith
  simpa [s, boundaryAngles_card p b hsep] using hs

theorem boundary_count_perimeter_four_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 2 ≤ (boundarySet p b).card) :
    ((boundarySet p b).card : ℝ) * (4 / 7 : ℝ) ≤ 2 * Real.pi := by
  have hsK : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    exact hK
  exact boundary_count_perimeter_bound_of_gaps p b (4 / 7) hsep hK hsK
    (fun i j hij => ordered_boundary_angle_gap_ge_four_sevenths
      p b hb hbB hsep i j hij)
    (ordered_boundary_wrap_gap_ge_four_sevenths p b hb hbB hsep hsK)

/-- At the candidate scale there are at most ten boundary centers.
The rational angle `4/7` was chosen so that eleven copies exceed `2π`. -/
theorem boundary_count_le_ten (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2) :
    (boundarySet p b).card ≤ 10 := by
  by_contra hnot
  have hK : 11 ≤ (boundarySet p b).card := by omega
  have hper := boundary_count_perimeter_four_sevenths p b hb hbB hsep (by omega)
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d20]
  have hKreal : (11 : ℝ) ≤ (boundarySet p b).card := by exact_mod_cast hK
  nlinarith

/-- At the candidate radius, separated centers have at most eleven boundary
points. The estimate uses the chord length bound, not inverse trigonometry. -/
theorem boundary_count_le_eleven (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2) :
    (boundarySet p b).card ≤ 11 := by
  by_contra hnot
  have hK : 12 ≤ (boundarySet p b).card := by omega
  have hper := boundary_count_perimeter_bound p b hb hsep (by omega)
  have hbq : b < (353 / 100 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_353_div_100
  have hpq : Real.pi < (3142 / 1000 : ℝ) := by
    linarith [Real.pi_lt_d20]
  have hprod : Real.pi * b < (3142 / 1000 : ℝ) * (353 / 100 : ℝ) := by
    calc
      Real.pi * b ≤ Real.pi * (353 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hbq.le Real.pi_pos.le
      _ < (3142 / 1000 : ℝ) * (353 / 100 : ℝ) :=
        mul_lt_mul_of_pos_right hpq (by norm_num)
  have hKreal : (12 : ℝ) ≤ (boundarySet p b).card := by exact_mod_cast hK
  have hper' : ((boundarySet p b).card : ℝ) * 2 ≤ 2 * Real.pi * b := by
    have hdiv := mul_le_mul_of_nonneg_right hper hb.le
    field_simp at hdiv ⊢
    nlinarith
  nlinarith

/-- The selected optimal representative simultaneously has `m ≤ 3` and
`K ≤ 10`. The ring-count conclusion does not depend on the selection rule. -/
theorem exists_optimal_selected_with_m_le_three_K_le_ten :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      (nonOuterIndices p b).card ≤ 3 ∧
      (boundarySet p b).card ≤ 10 := by
  obtain ⟨b, p, hbB, hopt, hp, hs, _hD, _hblock, _hFcap, _hFsmall, hm⟩ :=
    exists_optimal_selected_full
  have hb : 0 < b := by
    have := centerFeasible_radius_gt_two hopt.1
    linarith
  exact ⟨b, p, hbB, hopt, hp, hs, hm,
    boundary_count_le_ten p b hb hbB hs⟩

end CP15
