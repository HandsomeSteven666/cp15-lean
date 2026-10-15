import CP15.NonOuterCount

open scoped InnerProductSpace

namespace CP15

private theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg 2
  nlinarith

/-- Any two distinct non-outer centers have negative inner product, the
algebraic form of polar separation strictly greater than a right angle. -/
theorem nonOuter_pair_inner_neg {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hsep : Separated p 2)
    (hcap : ∀ k, ‖p k‖ < b → ¬TouchesOuter p b k → ‖p k‖ ≤ F b)
    (hF : F b < Real.sqrt 2)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ‖p i‖ < b ∧ ¬TouchesOuter p b i)
    (hj : ‖p j‖ < b ∧ ¬TouchesOuter p b j) :
    ⟪p i, p j⟫_ℝ < 0 := by
  have hri : ‖p i‖ < Real.sqrt 2 :=
    (hcap i hi.1 hi.2).trans_lt hF
  have hrj : ‖p j‖ < Real.sqrt 2 :=
    (hcap j hj.1 hj.2).trans_lt hF
  exact small_disk_pair_inner_neg (p i) (p j) hri hrj (hsep i j hij)

/-- Two distinct non-outer centers cannot include the origin when `F < √2`.
The separation constraint alone makes the second center too far out. -/
theorem nonOuter_pair_nonzero {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hsep : Separated p 2)
    (hcap : ∀ k, ‖p k‖ < b → ¬TouchesOuter p b k → ‖p k‖ ≤ F b)
    (hF : F b < Real.sqrt 2)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ‖p i‖ < b ∧ ¬TouchesOuter p b i)
    (hj : ‖p j‖ < b ∧ ¬TouchesOuter p b j) :
    p i ≠ 0 ∧ p j ≠ 0 := by
  have hFtwo : F b < 2 := hF.trans sqrt_two_lt_two
  constructor
  · intro hzero
    have hd := hsep i j hij
    have hjnorm : 2 ≤ ‖p j‖ := by simpa [hzero] using hd
    linarith [hcap j hj.1 hj.2]
  · intro hzero
    have hd := hsep j i (Ne.symm hij)
    have hinorm : 2 ≤ ‖p i‖ := by simpa [hzero] using hd
    linarith [hcap i hi.1 hi.2]

/-- A strict radial blocker of a nonzero non-outer center is an inner center
that itself touches the outer ring, provided the cap is below `√2`. -/
theorem nonOuter_blocker_touches_outer {n : ℕ} (p : Fin n → Plane)
    (b : ℝ) (hpack : InDisk b p ∧ Separated p 2)
    (hcap : ∀ k, ‖p k‖ < b → ¬TouchesOuter p b k → ‖p k‖ ≤ F b)
    (hF : F b < Real.sqrt 2)
    (hblock : ∀ k, ‖p k‖ < b → p k ≠ 0 →
      ∃ j, j ≠ k ∧ dist (p k) (p j) = 2 ∧
        ‖p k‖ ^ 2 < ⟪p j, p k⟫_ℝ)
    (i : Fin n) (hi : ‖p i‖ < b)
    (hno : ¬TouchesOuter p b i) (hnz : p i ≠ 0) :
    ∃ j : Fin n, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      ‖p j‖ < b ∧ 2 < ‖p j‖ ∧ TouchesOuter p b j ∧
      ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ := by
  obtain ⟨j, hji, hcontact, hdot⟩ := hblock i hi hnz
  have hjinner : ‖p j‖ < b := by
    have hjle := hpack.1 j
    by_contra hnot
    have hjboundary : ‖p j‖ = b := le_antisymm hjle (le_of_not_gt hnot)
    exact hno ⟨j, hji, hjboundary, hcontact⟩
  have hjradius := blocker_radius_sq (p i) (p j) hcontact hdot
  have hjgt : 2 < ‖p j‖ := by
    have hnonneg := norm_nonneg (p j)
    nlinarith [sq_nonneg ‖p i‖]
  have hjtouch : TouchesOuter p b j := by
    by_contra hnot
    have hjcap := hcap j hjinner hnot
    linarith [hF.trans sqrt_two_lt_two]
  exact ⟨j, hji, hcontact, hjinner, hjgt, hjtouch, hdot⟩

/-- Three non-outer centers force a strict cap-radius inequality. The
strictness comes from the radial blocker of the first center. -/
theorem three_nonOuter_F_sq_gt_four_thirds {n : ℕ}
    (p : Fin n → Plane) (b : ℝ) (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ q, ‖p q‖ < b → ‖p q‖ < D b)
    (hblock : ∀ q, ‖p q‖ < b → p q ≠ 0 →
      ∃ j, j ≠ q ∧ dist (p q) (p j) = 2 ∧
        ‖p q‖ ^ 2 < ⟪p j, p q⟫_ℝ)
    (hFcap : ∀ q, ‖p q‖ < b → ¬TouchesOuter p b q → ‖p q‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖p i‖ < b ∧ ¬TouchesOuter p b i)
    (hj : ‖p j‖ < b ∧ ¬TouchesOuter p b j)
    (hk : ‖p k‖ < b ∧ ¬TouchesOuter p b k) :
    4 / 3 < F b ^ 2 := by
  have hnz := (nonOuter_pair_nonzero p b hpack.2 hFcap hFsmall
    i j hij hi hj).1
  have histrict := nonouter_inner_cap_squared p b hb hpack hD hblock
    i hi.1 hnz hi.2
  have hrad : 0 ≤ D b ^ 2 - 4 := by
    nlinarith [sq_nonneg ‖p i‖]
  have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
    unfold F
    exact Real.sq_sqrt hrad
  rw [← hFsq] at histrict
  have hjle := hFcap j hj.1 hj.2
  have hkle := hFcap k hk.1 hk.2
  have hFnonneg : 0 ≤ F b := Real.sqrt_nonneg _
  have hjsq : ‖p j‖ ^ 2 ≤ F b ^ 2 := by
    nlinarith [norm_nonneg (p j)]
  have hksq : ‖p k‖ ^ 2 ≤ F b ^ 2 := by
    nlinarith [norm_nonneg (p k)]
  exact three_point_strict_radius_sq (p i) (p j) (p k) (F b)
    (hpack.2 i j hij) (hpack.2 j k hjk) (hpack.2 k i hki)
    histrict hjsq hksq

/-- Two non-outer centers force `F > 1`. The inequality is strict because
one center has the strict two-step radial blocker bound. -/
theorem two_nonOuter_F_gt_one {n : ℕ}
    (p : Fin n → Plane) (b : ℝ) (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ q, ‖p q‖ < b → ‖p q‖ < D b)
    (hblock : ∀ q, ‖p q‖ < b → p q ≠ 0 →
      ∃ j, j ≠ q ∧ dist (p q) (p j) = 2 ∧
        ‖p q‖ ^ 2 < ⟪p j, p q⟫_ℝ)
    (hFcap : ∀ q, ‖p q‖ < b → ¬TouchesOuter p b q → ‖p q‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ‖p i‖ < b ∧ ¬TouchesOuter p b i)
    (hj : ‖p j‖ < b ∧ ¬TouchesOuter p b j) :
    1 < F b := by
  have hnz := (nonOuter_pair_nonzero p b hpack.2 hFcap hFsmall
    i j hij hi hj).1
  have histrict := nonouter_inner_cap_squared p b hb hpack hD hblock
    i hi.1 hnz hi.2
  have hrad : 0 ≤ D b ^ 2 - 4 := by
    nlinarith [sq_nonneg ‖p i‖]
  have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
    unfold F
    exact Real.sq_sqrt hrad
  rw [← hFsq] at histrict
  have hFnonneg : 0 ≤ F b := Real.sqrt_nonneg _
  have hri : ‖p i‖ < F b := by
    nlinarith [norm_nonneg (p i)]
  have hrj := hFcap j hj.1 hj.2
  have htri : dist (p i) (p j) ≤ ‖p i‖ + ‖p j‖ := by
    simpa [dist_eq_norm] using norm_sub_le (p i) (p j)
  linarith [hpack.2 i j hij]

/-- One and the same selected optimal packing has the strict blocker,
both radial caps, the strict `F < √2` constant, and the `m ≤ 3` count. -/
theorem exists_optimal_selected_full :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → p i ≠ 0 →
        ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
          ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) ∧
      F b < Real.sqrt 2 ∧
      (nonOuterIndices p b).card ≤ 3 := by
  obtain ⟨b, hbB, hopt⟩ :=
    centerOptimal_exists_of_feasible Candidate.center_feasible
  have hb : 2 < b := centerFeasible_radius_gt_two hopt.1
  obtain ⟨p, hp, hs, hD, hblock⟩ :=
    exists_selected_inner_cap_and_blocker hb hopt.1
  have hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b := by
    intro i hi hno
    exact nonouter_F_cap p b hb ⟨hp, hs⟩ hD hblock i hi hno
  have hFsmall := Candidate.F_lt_sqrt_two_of_le_candidateB hb hbB
  exact ⟨b, p, hbB, hopt, hp, hs, hD, hblock, hFcap, hFsmall,
    nonOuter_count_le_three p b hs hFcap hFsmall⟩

/-- The optimal selected representative with the tie-break premises
retained. This is the representative needed for two-sided contact
arguments; it has the same caps and strict blocker as the earlier package. -/
theorem exists_optimal_selected_full_maximal :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      MaxBoundaryCount p b ∧ MaxSumAtBoundaryCount p b ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → p i ≠ 0 →
        ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
          ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) ∧
      F b < Real.sqrt 2 ∧
      (nonOuterIndices p b).card ≤ 3 := by
  obtain ⟨b, hbB, hopt⟩ :=
    centerOptimal_exists_of_feasible Candidate.center_feasible
  have hb : 2 < b := centerFeasible_radius_gt_two hopt.1
  obtain ⟨p, hp, hs, hK, hS, hD, hblock⟩ :=
    exists_selected_inner_cap_blocker_maximal hb hopt.1
  have hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b := by
    intro i hi hno
    exact nonouter_F_cap p b hb ⟨hp, hs⟩ hD hblock i hi hno
  have hFsmall := Candidate.F_lt_sqrt_two_of_le_candidateB hb hbB
  exact ⟨b, p, hbB, hopt, hp, hs, hK, hS, hD, hblock,
    hFcap, hFsmall,
    nonOuter_count_le_three p b hs hFcap hFsmall⟩

end CP15
