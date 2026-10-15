import CP15.StrongOuterGap

namespace CP15

private theorem abs_sin_half_le_sin_half_threshold
    (g θ : ℝ) (hg0 : 0 ≤ g) (hgθ : g ≤ θ)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi) :
    |Real.sin (g / 2)| ≤ Real.sin (θ / 2) := by
  have hhalf : 0 ≤ g / 2 ∧ g / 2 ≤ θ / 2 := by
    constructor <;> linarith
  have hsin0 : 0 ≤ Real.sin (g / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hhalf.1 (by linarith)
  rw [abs_of_nonneg hsin0]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith)
    (by linarith) hhalf.2

private theorem outer_angle_gap_ge_threshold
    (p : Fin 15 → Plane) (b θ : ℝ)
    (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hbsmall : b * Real.sin (θ / 2) < 1)
    (hsep : Separated p 2)
    (i j : BoundaryIndex p b) (hij : i.val ≠ j.val)
    (hangle : polarArg (p i.val) ≤ polarArg (p j.val)) :
    θ ≤ polarArg (p j.val) - polarArg (p i.val) := by
  by_contra hnot
  let g := polarArg (p j.val) - polarArg (p i.val)
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hgθ : g ≤ θ := by dsimp [g]; linarith
  have hs := abs_sin_half_le_sin_half_threshold g θ hg0 hgθ hθ0 hθpi
  have hc := boundary_chord_eq_sin (p i.val) (p j.val) b hb.le
    i.property j.property
  have heq : (polarArg (p i.val) - polarArg (p j.val)) / 2 = -(g / 2) := by
    dsimp [g]
    ring
  rw [heq, Real.sin_neg, abs_neg] at hc
  have hd := hsep i.val j.val hij
  have hle := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * b)
  rw [← hc] at hle
  nlinarith

private theorem outer_wrap_gap_ge_threshold
    (p : Fin 15 → Plane) (b θ : ℝ)
    (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hbsmall : b * Real.sin (θ / 2) < 1)
    (hsep : Separated p 2)
    (last first : BoundaryIndex p b) (hne : last.val ≠ first.val)
    (hangle : polarArg (p last.val) ≤
      polarArg (p first.val) + 2 * Real.pi) :
    θ ≤ polarArg (p first.val) + 2 * Real.pi -
      polarArg (p last.val) := by
  by_contra hnot
  let g := polarArg (p first.val) + 2 * Real.pi - polarArg (p last.val)
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hgθ : g ≤ θ := by dsimp [g]; linarith
  have hs := abs_sin_half_le_sin_half_threshold g θ hg0 hgθ hθ0 hθpi
  have hc := boundary_chord_eq_sin (p last.val) (p first.val) b hb.le
    last.property first.property
  have heq : (polarArg (p last.val) - polarArg (p first.val)) / 2 =
      Real.pi - g / 2 := by dsimp [g]; ring
  rw [heq, Real.sin_pi_sub] at hc
  have hd := hsep last.val first.val hne
  have hle := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * b)
  rw [← hc] at hle
  nlinarith

private theorem ordered_boundary_angle_gap_ge_threshold
    (p : Fin 15 → Plane) (b θ : ℝ)
    (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hbsmall : b * Real.sin (θ / 2) < 1)
    (hsep : Separated p 2)
    (i j : Fin (boundaryAngles p b).card) (hij : i < j) :
    θ ≤ (boundaryAngles p b).orderEmbOfFin rfl j -
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
  have hgap := outer_angle_gap_ge_threshold p b θ hb hθ0 hθpi
    hbsmall hsep u v hne (by linarith [hu, hv])
  simpa only [hu, hv] using hgap

private theorem ordered_boundary_wrap_gap_ge_threshold
    (p : Fin 15 → Plane) (b θ : ℝ)
    (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hbsmall : b * Real.sin (θ / 2) < 1)
    (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card) :
    θ ≤ (boundaryAngles p b).orderEmbOfFin rfl ⟨0, by omega⟩ +
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
  have hgap := outer_wrap_gap_ge_threshold p b θ hb hθ0 hθpi
    hbsmall hsep v u hne hwrap
  simpa only [hu, hv, s, e, first, last] using hgap

/-- Any rational threshold whose half-sine is small enough for the
candidate radius bounds every actual cyclic outer gap. -/
theorem every_next_gap_ge_threshold (p : Fin 15 → Plane) (b θ : ℝ)
    (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hbsmall : b * Real.sin (θ / 2) < 1)
    (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card) :
    θ ≤ nextBoundaryGap p b hK u := by
  by_cases hu : u.val + 1 < (boundaryAngles p b).card
  · have hlt : u < (⟨u.val + 1, hu⟩ : Fin (boundaryAngles p b).card) := by
      change u.val < u.val + 1
      omega
    simpa [nextBoundaryGap, hu] using
      ordered_boundary_angle_gap_ge_threshold p b θ hb hθ0 hθpi
        hbsmall hsep u ⟨u.val + 1, hu⟩ hlt
  · have huval : u.val = (boundaryAngles p b).card - 1 := by
      have := u.isLt
      omega
    have hlast : u = (⟨(boundaryAngles p b).card - 1, by omega⟩ :
        Fin (boundaryAngles p b).card) := Fin.ext huval
    have hnot : ¬(boundaryAngles p b).card - 1 + 1 <
        (boundaryAngles p b).card := by omega
    simpa [nextBoundaryGap, hlast, hnot] using
      ordered_boundary_wrap_gap_ge_threshold p b θ hb hθ0 hθpi
        hbsmall hsep hK

/-- A tighter exact rational gap threshold for the nine-boundary budget. -/
theorem every_next_gap_ge_57588_div_100000
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card) :
    (57588 / 100000 : ℝ) ≤ nextBoundaryGap p b hK u := by
  have hbq : b < (352136 / 100000 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_352136_div_100000
  have hsin : Real.sin (57588 / 200000 : ℝ) <
      (100000 / 352136 : ℝ) := by
    have h := Real.sin_bound (x := (57588 / 200000 : ℝ)) (by norm_num)
    have habs := (abs_le.mp h).2
    norm_num at habs ⊢
    nlinarith
  have hsinpos : 0 < Real.sin (57588 / 200000 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num)
      (by linarith [Real.pi_gt_three])
  have hbsmall : b * Real.sin ((57588 / 100000 : ℝ) / 2) < 1 := by
    have hprod : b * Real.sin (57588 / 200000 : ℝ) < 1 := by
      calc
        b * Real.sin (57588 / 200000 : ℝ) <
            (352136 / 100000 : ℝ) * Real.sin (57588 / 200000 : ℝ) :=
          mul_lt_mul_of_pos_right hbq hsinpos
        _ < (352136 / 100000 : ℝ) * (100000 / 352136 : ℝ) :=
          mul_lt_mul_of_pos_left hsin (by norm_num)
        _ = 1 := by norm_num
    convert hprod using 1 <;> norm_num
  exact every_next_gap_ge_threshold p b (57588 / 100000) hb
    (by norm_num) (by linarith [Real.pi_gt_three]) hbsmall hsep hK u

end CP15
