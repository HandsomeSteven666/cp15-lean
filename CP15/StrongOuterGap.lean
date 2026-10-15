import CP15.CollisionGeometry

namespace CP15

private theorem sin_23_div_80_lt_500_div_1761 :
    Real.sin (23 / 80 : ℝ) < 500 / 1761 := by
  have h := Real.sin_bound (x := (23 / 80 : ℝ)) (by norm_num)
  have habs := (abs_le.mp h).2
  norm_num at habs ⊢
  nlinarith

private theorem abs_sin_half_le_sin_23_div_80 (g : ℝ)
    (hg0 : 0 ≤ g) (hghi : g ≤ 23 / 40) :
    |Real.sin (g / 2)| ≤ Real.sin (23 / 80 : ℝ) := by
  have hpi := Real.pi_gt_three
  have hhalf : 0 ≤ g / 2 ∧ g / 2 ≤ 23 / 80 := by
    constructor <;> linarith
  have hsin0 : 0 ≤ Real.sin (g / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hhalf.1 (by linarith)
  rw [abs_of_nonneg hsin0]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith)
    (by linarith) hhalf.2

private theorem b_sin_23_div_80_lt_one (b : ℝ)
    (hbB : b ≤ candidateB) : b * Real.sin (23 / 80 : ℝ) < 1 := by
  have hbq : b < (1761 / 500 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_1761_div_500
  have hsinpos : 0 < Real.sin (23 / 80 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num)
      (by linarith [Real.pi_gt_three])
  calc
    b * Real.sin (23 / 80 : ℝ) <
        (1761 / 500 : ℝ) * Real.sin (23 / 80 : ℝ) :=
      mul_lt_mul_of_pos_right hbq hsinpos
    _ < (1761 / 500 : ℝ) * (500 / 1761 : ℝ) :=
      mul_lt_mul_of_pos_left sin_23_div_80_lt_500_div_1761 (by norm_num)
    _ = 1 := by norm_num

private theorem outer_angle_gap_ge_23_div_40 (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (i j : BoundaryIndex p b) (hij : i.val ≠ j.val)
    (hangle : polarArg (p i.val) ≤ polarArg (p j.val)) :
    (23 / 40 : ℝ) ≤ polarArg (p j.val) - polarArg (p i.val) := by
  by_contra hnot
  let g := polarArg (p j.val) - polarArg (p i.val)
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hghi : g ≤ (23 / 40 : ℝ) := by dsimp [g]; linarith
  have hs := abs_sin_half_le_sin_23_div_80 g hg0 hghi
  have hc := boundary_chord_eq_sin (p i.val) (p j.val) b hb.le
    i.property j.property
  have heq : (polarArg (p i.val) - polarArg (p j.val)) / 2 = -(g / 2) := by
    dsimp [g]
    ring
  rw [heq, Real.sin_neg, abs_neg] at hc
  have hd := hsep i.val j.val hij
  have hbsmall := b_sin_23_div_80_lt_one b hbB
  have hle := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * b)
  rw [← hc] at hle
  nlinarith

private theorem outer_wrap_gap_ge_23_div_40 (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (last first : BoundaryIndex p b) (hne : last.val ≠ first.val)
    (hangle : polarArg (p last.val) ≤
      polarArg (p first.val) + 2 * Real.pi) :
    (23 / 40 : ℝ) ≤ polarArg (p first.val) + 2 * Real.pi -
      polarArg (p last.val) := by
  by_contra hnot
  let g := polarArg (p first.val) + 2 * Real.pi - polarArg (p last.val)
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hghi : g ≤ (23 / 40 : ℝ) := by dsimp [g]; linarith
  have hs := abs_sin_half_le_sin_23_div_80 g hg0 hghi
  have hc := boundary_chord_eq_sin (p last.val) (p first.val) b hb.le
    last.property first.property
  have heq : (polarArg (p last.val) - polarArg (p first.val)) / 2 =
      Real.pi - g / 2 := by dsimp [g]; ring
  rw [heq, Real.sin_pi_sub] at hc
  have hd := hsep last.val first.val hne
  have hbsmall := b_sin_23_div_80_lt_one b hbB
  have hle := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * b)
  rw [← hc] at hle
  nlinarith

private theorem ordered_boundary_angle_gap_ge_23_div_40
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (i j : Fin (boundaryAngles p b).card) (hij : i < j) :
    (23 / 40 : ℝ) ≤
      (boundaryAngles p b).orderEmbOfFin rfl j -
        (boundaryAngles p b).orderEmbOfFin rfl i := by
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  have hi : e i ∈ s := Finset.orderEmbOfFin_mem s rfl i
  have hj : e j ∈ s := Finset.orderEmbOfFin_mem s rfl j
  obtain ⟨u, hu⟩ := (boundaryAngles_mem p b (e i)).mp hi
  obtain ⟨v, hv⟩ := (boundaryAngles_mem p b (e j)).mp hj
  have hlt : e i < e j := e.strictMono hij
  have hne : u.val ≠ v.val := by
    intro heq
    rw [heq] at hu
    linarith
  have hgap := outer_angle_gap_ge_23_div_40 p b hb hbB hsep u v hne
    (by linarith [hu, hv])
  simpa only [hu, hv] using hgap

private theorem ordered_boundary_wrap_gap_ge_23_div_40
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card) :
    (23 / 40 : ℝ) ≤
      (boundaryAngles p b).orderEmbOfFin rfl ⟨0, by omega⟩ +
        2 * Real.pi -
        (boundaryAngles p b).orderEmbOfFin rfl
          ⟨(boundaryAngles p b).card - 1, by omega⟩ := by
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  let first : Fin s.card := ⟨0, by dsimp [s]; omega⟩
  let last : Fin s.card := ⟨s.card - 1, by dsimp [s]; omega⟩
  have hfl : first < last := by
    change 0 < s.card - 1
    dsimp [s]
    omega
  have hfirst : e first ∈ s := Finset.orderEmbOfFin_mem s rfl first
  have hlast : e last ∈ s := Finset.orderEmbOfFin_mem s rfl last
  obtain ⟨u, hu⟩ := (boundaryAngles_mem p b (e first)).mp hfirst
  obtain ⟨v, hv⟩ := (boundaryAngles_mem p b (e last)).mp hlast
  have hlt : e first < e last := e.strictMono hfl
  have hne : v.val ≠ u.val := by
    intro heq
    rw [heq] at hv
    linarith
  have hrange_first := polarArg_range (p u.val)
  have hrange_last := polarArg_range (p v.val)
  have hwrap : polarArg (p v.val) ≤ polarArg (p u.val) + 2 * Real.pi := by
    linarith
  have hgap := outer_wrap_gap_ge_23_div_40 p b hb hbB hsep v u hne hwrap
  simpa only [hu, hv, s, e, first, last] using hgap

/-- Uniform rational lower bound for every actual cyclic boundary gap. -/
theorem every_next_gap_ge_23_div_40 (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card) :
    (23 / 40 : ℝ) ≤ nextBoundaryGap p b hK u := by
  by_cases hu : u.val + 1 < (boundaryAngles p b).card
  · have hlt : u < (⟨u.val + 1, hu⟩ : Fin (boundaryAngles p b).card) := by
      change u.val < u.val + 1
      omega
    simpa [nextBoundaryGap, hu] using
      ordered_boundary_angle_gap_ge_23_div_40 p b hb hbB hsep
        u ⟨u.val + 1, hu⟩ hlt
  · have huval : u.val = (boundaryAngles p b).card - 1 := by
      have := u.isLt
      omega
    have hlast : u = (⟨(boundaryAngles p b).card - 1, by omega⟩ :
        Fin (boundaryAngles p b).card) := Fin.ext huval
    have hnot : ¬(boundaryAngles p b).card - 1 + 1 <
        (boundaryAngles p b).card := by omega
    simpa [nextBoundaryGap, hlast, hnot] using
      ordered_boundary_wrap_gap_ge_23_div_40 p b hb hbB hsep hK

/-- The shared-blocker radius threshold makes its contact offset larger
than `5/9` radians. The algebraic comparison is made at rational enclosures
of the candidate radius and shared-blocker radius. -/
theorem capped_shared_contact_offset_gt_five_ninths
    (b s δ : ℝ) (hb3 : 3 < b) (hbB : b ≤ candidateB)
    (hs2 : (16 / 3 : ℝ) < s ^ 2) (hspos : 0 ≤ s)
    (hsD : s < D b) (hδ0 : 0 ≤ δ)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    (5 / 9 : ℝ) < δ := by
  let q : ℝ := 1761 / 500
  let t : ℝ := 2309 / 1000
  let c : ℝ := 137 / 81
  have hbq : b < q := by
    dsimp [q]
    exact hbB.trans_lt Candidate.candidateB_lt_1761_div_500
  have hslo : t < s := by
    dsimp [t]
    nlinarith
  have hshi : s < (12 / 5 : ℝ) :=
    hsD.trans (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)
  have hfactorb : 0 < (q - b) * (q + b - c * s) := by
    apply mul_pos (by linarith)
    dsimp [q, c]
    nlinarith
  have hfactors : (s - t) * (s + t - c * q) < 0 := by
    apply mul_neg_of_pos_of_neg (by linarith)
    dsimp [t, c, q]
    linarith
  have hpoly : b ^ 2 + s ^ 2 - 4 < c * b * s := by
    have hcorner : q ^ 2 + t ^ 2 - 4 < c * q * t := by
      dsimp [q, t, c]
      norm_num
    nlinarith [hfactorb, hfactors]
  have hscale : 0 < 2 * s * b := by positivity
  have hcos : Real.cos δ < (137 / 162 : ℝ) := by
    dsimp [c] at hpoly
    nlinarith
  by_contra hnot
  have hδhi : δ ≤ (5 / 9 : ℝ) := le_of_not_gt hnot
  have hδsq : δ ^ 2 ≤ (5 / 9 : ℝ) ^ 2 := by nlinarith
  have hTaylor := Real.one_sub_sq_div_two_le_cos (x := δ)
  nlinarith

end CP15
