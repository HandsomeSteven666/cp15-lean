import CP15.BoundaryOrder

namespace CP15

/-- The unit circle exponential is one-Lipschitz in its real angle. -/
theorem exp_I_chord_le_angle (θ φ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ ≤ |θ - φ| := by
  have hfactor : Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I) =
      Complex.exp (φ * Complex.I) *
        (Complex.exp ((θ - φ) * Complex.I) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    have heq : φ * Complex.I + (θ - φ) * Complex.I = θ * Complex.I := by ring
    rw [heq]
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I]
  simpa [mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - φ))

/-- Exact unit-circle chord identity. -/
theorem exp_I_chord_eq_sin (θ φ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ =
      2 * |Real.sin ((θ - φ) / 2)| := by
  have hfactor : Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I) =
      Complex.exp (φ * Complex.I) *
        (Complex.exp ((θ - φ) * Complex.I) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    have heq : φ * Complex.I + (θ - φ) * Complex.I = θ * Complex.I := by ring
    rw [heq]
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I]
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (θ - φ)
  simpa [mul_comm, Real.norm_eq_abs, abs_mul] using h

theorem sin_two_sevenths_lt_100_div_353 :
    Real.sin (2 / 7 : ℝ) < 100 / 353 := by
  have h := Real.sin_bound (x := (2 / 7 : ℝ)) (by norm_num)
  have habs := (abs_le.mp h).2
  norm_num at habs ⊢
  nlinarith

theorem abs_sin_half_le_sin_two_sevenths (g : ℝ)
    (hg0 : 0 ≤ g) (hg4 : g ≤ 4 / 7) :
    |Real.sin (g / 2)| ≤ Real.sin (2 / 7 : ℝ) := by
  have hpi := Real.pi_gt_three
  have hhalf : 0 ≤ g / 2 ∧ g / 2 ≤ 2 / 7 := by constructor <;> linarith
  have hsin0 : 0 ≤ Real.sin (g / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hhalf.1 (by linarith)
  rw [abs_of_nonneg hsin0]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith)
    (by linarith) hhalf.2

theorem b_sin_two_sevenths_lt_one (b : ℝ) (hbB : b ≤ candidateB) :
    b * Real.sin (2 / 7 : ℝ) < 1 := by
  have hbq : b < (353 / 100 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_353_div_100
  have hsinpos : 0 < Real.sin (2 / 7 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  calc
    b * Real.sin (2 / 7 : ℝ) <
        (353 / 100 : ℝ) * Real.sin (2 / 7 : ℝ) :=
      mul_lt_mul_of_pos_right hbq hsinpos
    _ < (353 / 100 : ℝ) * (100 / 353 : ℝ) :=
      mul_lt_mul_of_pos_left sin_two_sevenths_lt_100_div_353 (by norm_num)
    _ = 1 := by norm_num

/-- A chord of a circle is no longer than its radius times the difference
of any two chosen polar arguments. No small-angle hypothesis is needed. -/
theorem boundary_chord_le_angle (x y : Plane) (b : ℝ)
    (hb : 0 ≤ b) (hx : ‖x‖ = b) (hy : ‖y‖ = b) :
    dist x y ≤ b * |polarArg x - polarArg y| := by
  have hc : dist x y = ‖planeComplex x - planeComplex y‖ := by
    rw [dist_eq_norm]
    have heq : planeComplex (x - y) = planeComplex x - planeComplex y := by
      apply Complex.ext <;> simp [planeComplex]
    rw [← heq, planeComplex_norm]
  rw [hc]
  have hrep_x : planeComplex x = (b : ℂ) * Complex.exp (polarArg x * Complex.I) := by
    simpa [polarArg, planeComplex_norm, hx] using
      (Complex.norm_mul_exp_arg_mul_I (planeComplex x)).symm
  have hrep_y : planeComplex y = (b : ℂ) * Complex.exp (polarArg y * Complex.I) := by
    simpa [polarArg, planeComplex_norm, hy] using
      (Complex.norm_mul_exp_arg_mul_I (planeComplex y)).symm
  rw [hrep_x, hrep_y, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb]
  exact mul_le_mul_of_nonneg_left (exp_I_chord_le_angle _ _) hb

theorem boundary_chord_eq_sin (x y : Plane) (b : ℝ)
    (hb : 0 ≤ b) (hx : ‖x‖ = b) (hy : ‖y‖ = b) :
    dist x y = 2 * b * |Real.sin ((polarArg x - polarArg y) / 2)| := by
  have hc : dist x y = ‖planeComplex x - planeComplex y‖ := by
    rw [dist_eq_norm]
    have heq : planeComplex (x - y) = planeComplex x - planeComplex y := by
      apply Complex.ext <;> simp [planeComplex]
    rw [← heq, planeComplex_norm]
  rw [hc]
  have hrep_x : planeComplex x = (b : ℂ) * Complex.exp (polarArg x * Complex.I) := by
    simpa [polarArg, planeComplex_norm, hx] using
      (Complex.norm_mul_exp_arg_mul_I (planeComplex x)).symm
  have hrep_y : planeComplex y = (b : ℂ) * Complex.exp (polarArg y * Complex.I) := by
    simpa [polarArg, planeComplex_norm, hy] using
      (Complex.norm_mul_exp_arg_mul_I (planeComplex y)).symm
  rw [hrep_x, hrep_y, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb, exp_I_chord_eq_sin]
  ring

theorem exp_I_add_two_pi (θ : ℝ) :
    Complex.exp ((θ + 2 * Real.pi) * Complex.I) =
      Complex.exp (θ * Complex.I) := by
  rw [add_mul, Complex.exp_add]
  rw [Complex.exp_two_pi_mul_I, mul_one]

/-- The same chord estimate measured across the branch cut of polar argument. -/
theorem boundary_chord_le_wrap (x y : Plane) (b : ℝ)
    (hb : 0 ≤ b) (hx : ‖x‖ = b) (hy : ‖y‖ = b) :
    dist x y ≤ b * |polarArg y + 2 * Real.pi - polarArg x| := by
  have hc : dist x y = ‖planeComplex x - planeComplex y‖ := by
    rw [dist_eq_norm]
    have heq : planeComplex (x - y) = planeComplex x - planeComplex y := by
      apply Complex.ext <;> simp [planeComplex]
    rw [← heq, planeComplex_norm]
  rw [hc]
  have hrep_x : planeComplex x = (b : ℂ) * Complex.exp (polarArg x * Complex.I) := by
    simpa [polarArg, planeComplex_norm, hx] using
      (Complex.norm_mul_exp_arg_mul_I (planeComplex x)).symm
  have hrep_y : planeComplex y = (b : ℂ) *
      Complex.exp ((polarArg y + 2 * Real.pi) * Complex.I) := by
    rw [exp_I_add_two_pi]
    simpa [polarArg, planeComplex_norm, hy] using
      (Complex.norm_mul_exp_arg_mul_I (planeComplex y)).symm
  rw [hrep_x, hrep_y, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb]
  have h := exp_I_chord_le_angle (polarArg x) (polarArg y + 2 * Real.pi)
  rw [abs_sub_comm] at h
  convert mul_le_mul_of_nonneg_left h hb using 1 <;> (push_cast; ring)

/-- This weaker angular separation is enough for the eight-gap argument. -/
theorem outer_angle_gap_ge_two_div (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hsep : Separated p 2)
    (i j : BoundaryIndex p b) (hij : i.val ≠ j.val)
    (hangle : polarArg (p i.val) ≤ polarArg (p j.val)) :
    2 / b ≤ polarArg (p j.val) - polarArg (p i.val) := by
  have hd := hsep i.val j.val hij
  have hchord := boundary_chord_le_angle (p i.val) (p j.val) b hb.le
    i.property j.property
  have hnonneg : 0 ≤ polarArg (p j.val) - polarArg (p i.val) := sub_nonneg.mpr hangle
  rw [abs_sub_comm, abs_of_nonneg hnonneg] at hchord
  apply (div_le_iff₀ hb).2
  nlinarith

/-- Rational angular separation using the fifth-order sine enclosure.
This is stronger than the elementary arc-length bound at the candidate scale. -/
theorem outer_angle_gap_ge_four_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (i j : BoundaryIndex p b) (hij : i.val ≠ j.val)
    (hangle : polarArg (p i.val) ≤ polarArg (p j.val)) :
    (4 / 7 : ℝ) ≤ polarArg (p j.val) - polarArg (p i.val) := by
  by_contra hnot
  let g := polarArg (p j.val) - polarArg (p i.val)
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hg4 : g ≤ (4 / 7 : ℝ) := by dsimp [g]; linarith
  have hs := abs_sin_half_le_sin_two_sevenths g hg0 hg4
  have hc := boundary_chord_eq_sin (p i.val) (p j.val) b hb.le
    i.property j.property
  have heq : (polarArg (p i.val) - polarArg (p j.val)) / 2 = -(g / 2) := by
    dsimp [g]
    ring
  rw [heq, Real.sin_neg, abs_neg] at hc
  have hd := hsep i.val j.val hij
  have hbsmall := b_sin_two_sevenths_lt_one b hbB
  have hle := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * b)
  rw [← hc] at hle
  nlinarith

theorem outer_wrap_gap_ge_two_div (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hsep : Separated p 2)
    (last first : BoundaryIndex p b) (hne : last.val ≠ first.val)
    (hangle : polarArg (p last.val) ≤
      polarArg (p first.val) + 2 * Real.pi) :
    2 / b ≤ polarArg (p first.val) + 2 * Real.pi - polarArg (p last.val) := by
  have hd := hsep last.val first.val hne
  have hchord := boundary_chord_le_wrap (p last.val) (p first.val) b hb.le
    last.property first.property
  have hnonneg : 0 ≤ polarArg (p first.val) + 2 * Real.pi -
      polarArg (p last.val) := sub_nonneg.mpr hangle
  rw [abs_of_nonneg hnonneg] at hchord
  apply (div_le_iff₀ hb).2
  nlinarith

theorem outer_wrap_gap_ge_four_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (last first : BoundaryIndex p b) (hne : last.val ≠ first.val)
    (hangle : polarArg (p last.val) ≤
      polarArg (p first.val) + 2 * Real.pi) :
    (4 / 7 : ℝ) ≤ polarArg (p first.val) + 2 * Real.pi -
      polarArg (p last.val) := by
  by_contra hnot
  let g := polarArg (p first.val) + 2 * Real.pi - polarArg (p last.val)
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hg4 : g ≤ (4 / 7 : ℝ) := by dsimp [g]; linarith
  have hs := abs_sin_half_le_sin_two_sevenths g hg0 hg4
  have hc := boundary_chord_eq_sin (p last.val) (p first.val) b hb.le
    last.property first.property
  have heq : (polarArg (p last.val) - polarArg (p first.val)) / 2 =
      Real.pi - g / 2 := by dsimp [g]; ring
  rw [heq, Real.sin_pi_sub] at hc
  have hd := hsep last.val first.val hne
  have hbsmall := b_sin_two_sevenths_lt_one b hbB
  have hle := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * b)
  rw [← hc] at hle
  nlinarith

/-- Every ordered pair of distinct boundary angles has the basic lower
separation. In particular it applies to every ordinary consecutive gap. -/
theorem ordered_boundary_angle_gap_ge_two_div (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hsep : Separated p 2)
    (i j : Fin (boundaryAngles p b).card) (hij : i < j) :
    2 / b ≤
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
  have hgap := outer_angle_gap_ge_two_div p b hb hsep u v hne (by linarith [hu, hv])
  simpa only [hu, hv] using hgap

theorem ordered_boundary_angle_gap_ge_four_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (i j : Fin (boundaryAngles p b).card) (hij : i < j) :
    (4 / 7 : ℝ) ≤
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
  have hgap := outer_angle_gap_ge_four_sevenths p b hb hbB hsep u v hne
    (by linarith [hu, hv])
  simpa only [hu, hv] using hgap

/-- The closing gap from the greatest to the least boundary angle satisfies
the same separation bound. The polar branch cut is handled explicitly. -/
theorem ordered_boundary_wrap_gap_ge_two_div (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card) :
    2 / b ≤
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
  have hgap := outer_wrap_gap_ge_two_div p b hb hsep v u hne hwrap
  simpa only [hu, hv, s, e, first, last] using hgap

theorem ordered_boundary_wrap_gap_ge_four_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card) :
    (4 / 7 : ℝ) ≤
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
  have hgap := outer_wrap_gap_ge_four_sevenths p b hb hbB hsep v u hne hwrap
  simpa only [hu, hv, s, e, first, last] using hgap

end CP15
