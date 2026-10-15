import CP15.M2K9DistinctHalfCutoffScalar

open scoped InnerProductSpace

namespace CP15

/-- The sharper outer-radius cutoff uses correlated core radii. Treating
the two blocker lower radii independently loses the strict margin. -/
theorem distinct_m2_K9_requires_b_gt_seven_halves
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
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
    (hblockerNe : blocker 0 ≠ blocker 1) : (7 / 2 : ℝ) < b := by
  have hb17 := m2_radius_gt_seventeen_fifths p b hb hpack hD hblock
    hFcap hFsmall (by omega)
  have hb3 : 3 < b := by linarith
  have hbpos : 0 < b := by linarith
  by_contra hnot
  have hb7 : b ≤ 7 / 2 := le_of_not_gt hnot
  have hDle : D b ≤ 33 / 14 := by
    have hrec : (8 / 7 : ℝ) ≤ 4 / b := by
      apply (le_div_iff₀ hbpos).2
      linarith
    unfold D
    linarith
  have hFle : F b ≤ 5 / 4 := by
    have hDpos := D_pos hb
    have harg : D b ^ 2 - 4 ≤ (5 / 4 : ℝ) ^ 2 := by nlinarith
    by_cases hrad : 0 ≤ D b ^ 2 - 4
    · have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
        unfold F
        exact Real.sq_sqrt hrad
      have hFn : 0 ≤ F b := Real.sqrt_nonneg _
      nlinarith
    · have hFzero : F b = 0 := by
        unfold F
        exact Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hrad)
      rw [hFzero]
      norm_num
  have hcoreHi (c : Fin 2) : ‖p (target c)‖ ≤ 5 / 4 :=
    (hFcap (target c) (hno c).1 (hno c).2).trans hFle
  have hsum : (2 : ℝ) ≤ ‖p (target 0)‖ + ‖p (target 1)‖ := by
    have hd := hpack.2 _ _ (htarget.ne (by decide : (0 : Fin 2) ≠ 1))
    have ht : dist (p (target 0)) (p (target 1)) ≤
        ‖p (target 0)‖ + ‖p (target 1)‖ := by
      simpa [dist_eq_norm] using norm_sub_le (p (target 0)) (p (target 1))
    exact hd.trans ht
  have hbig : 1 ≤ ‖p (target 0)‖ ∨ 1 ≤ ‖p (target 1)‖ := by
    by_cases h0 : 1 ≤ ‖p (target 0)‖
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  have hsHi (c : Fin 2) : ‖p (blocker c)‖ ≤ 12 / 5 :=
    ((hD (blocker c) (hdata c).2.2.1).trans
      (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)).le
  have hsSq (c : Fin 2) :
      4 + ‖p (target c)‖ ^ 2 < ‖p (blocker c)‖ ^ 2 := by
    have h := blocker_radius_sq (p (target c)) (p (blocker c))
      (hdata c).2.1 (hdata c).2.2.2.2.2.2.2
    linarith
  let θ : ℝ := 57949 / 100000
  have hθ0 : 0 ≤ θ := by dsimp [θ]; norm_num
  have hθpi : θ ≤ Real.pi := by dsimp [θ]; linarith [Real.pi_gt_three]
  have hsinUpper : Real.sin (θ / 2) < 2 / 7 := by
    have hbound := Real.sin_bound (x := θ / 2) (by dsimp [θ]; norm_num)
    have h := (abs_le.mp hbound).2
    norm_num [θ] at h ⊢
    linarith
  have hsin0 : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by dsimp [θ]; norm_num)
      (by dsimp [θ]; linarith [Real.pi_gt_three])
  have hbsmall : b * Real.sin (θ / 2) < 1 := by
    calc
      b * Real.sin (θ / 2) ≤ (7 / 2 : ℝ) * Real.sin (θ / 2) :=
        mul_le_mul_of_nonneg_right hb7 hsin0.le
      _ < (7 / 2 : ℝ) * (2 / 7) :=
        mul_lt_mul_of_pos_left hsinUpper (by norm_num)
      _ = 1 := by norm_num
  have hinj : Function.Injective blocker := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hpack.2, hK9]
    norm_num
  obtain ⟨charge, δ, hcharge, hδ, hbudget⟩ :=
    exists_distinct_two_contact_threshold_budget p b hb hbB hpack hD hK9 hsize
      blocker outer hinj (fun c => (hdata c).2.2.1)
      (fun c => (hdata c).2.2.2.1.le)
      (fun c => (hdata c).2.2.2.2.2.1)
      (fun c => (hdata c).2.2.2.2.2.2.1) θ hθ0 hθpi hbsmall
  have hδpi (c : Fin 2) : δ c ≤ Real.pi := by
    have hg := every_next_gap_lt_pi p b hbpos hbB hpack.2 (by omega) (charge c)
    linarith [(hδ c).2.1]
  rw [Fin.sum_univ_two] at hbudget
  dsimp [θ] at hbudget
  rcases hbig with h0 | h1
  · exact distinct_half_cutoff_scalar_certificate b
      ‖p (target 0)‖ ‖p (target 1)‖ ‖p (blocker 0)‖ ‖p (blocker 1)‖
      (δ 0) (δ 1) hb3 hb7 h0 (hcoreHi 0) (norm_nonneg _) hsum
      (hdata 0).2.2.2.1 (hsHi 0) (hdata 1).2.2.2.1 (hsHi 1)
      (hsSq 0) (hsSq 1) (by linarith [(hδ 0).1]) (hδpi 0)
      (by linarith [(hδ 1).1]) (hδpi 1) (hδ 0).2.2.1 (hδ 1).2.2.1 hbudget
  · exact distinct_half_cutoff_scalar_certificate b
      ‖p (target 1)‖ ‖p (target 0)‖ ‖p (blocker 1)‖ ‖p (blocker 0)‖
      (δ 1) (δ 0) hb3 hb7 h1 (hcoreHi 1) (norm_nonneg _) (by linarith)
      (hdata 1).2.2.2.1 (hsHi 1) (hdata 0).2.2.2.1 (hsHi 0)
      (hsSq 1) (hsSq 0) (by linarith [(hδ 1).1]) (hδpi 1)
      (by linarith [(hδ 0).1]) (hδpi 0) (hδ 1).2.2.1 (hδ 0).2.2.1 (by linarith)

end CP15
