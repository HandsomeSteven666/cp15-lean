import CP15.M2K9DistinctAngles

open scoped InnerProductSpace

namespace CP15

/-- In the open radius-two disk, a separated pair has polar angle
strictly larger than sixty degrees. This includes unequal radii. -/
theorem open_two_pair_cos_lt_half (x y : Plane)
    (hx : ‖x‖ < 2) (hy : ‖y‖ < 2) (hsep : 2 ≤ dist x y) :
    Real.cos (polarArg x - polarArg y) < 1 / 2 := by
  have hxn := norm_nonneg x
  have hyn := norm_nonneg y
  have hdist : 4 ≤ dist x y ^ 2 := by nlinarith [dist_nonneg (x := x) (y := y)]
  rw [dist_eq_norm, norm_sub_sq_real, polar_inner] at hdist
  by_contra hnot
  have hc : (1 / 2 : ℝ) ≤ Real.cos (polarArg x - polarArg y) :=
    le_of_not_gt hnot
  have hprod : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg hxn hyn
  have hcos := mul_le_mul_of_nonneg_left hc hprod
  by_cases hxy : ‖x‖ ≤ ‖y‖
  · have hdiff : 0 ≤ ‖x‖ * (‖y‖ - ‖x‖) := mul_nonneg hxn (by linarith)
    nlinarith
  · have hdiff : 0 ≤ ‖y‖ * (‖x‖ - ‖y‖) := mul_nonneg hyn (by linarith)
    nlinarith

private theorem open_two_polar_injective (q : Fin 6 → Plane)
    (hsep : Separated q 2) (hsmall : ∀ i, ‖q i‖ < 2) :
    Function.Injective (fun i => polarArg (q i)) := by
  intro i j harg
  by_contra hij
  have h := open_two_pair_cos_lt_half (q i) (q j) (hsmall i) (hsmall j)
    (hsep i j hij)
  change polarArg (q i) = polarArg (q j) at harg
  rw [harg, sub_self, Real.cos_zero] at h
  norm_num at h

/-- The six-point disk obstruction, proved by sorting actual polar
arguments and summing all six cyclic gaps, including the branch cut. -/
theorem six_point_open_two_obstruction (q : Fin 6 → Plane)
    (hsep : Separated q 2) (hsmall : ∀ i, ‖q i‖ < 2) : False := by
  classical
  have hpolar := open_two_polar_injective q hsep hsmall
  let angles : Finset ℝ := Finset.univ.image (fun i => polarArg (q i))
  have hcard : angles.card = 6 := by
    dsimp [angles]
    simpa using Finset.card_image_of_injective Finset.univ hpolar
  let order := angles.orderEmbOfFin rfl
  let ix (i : Fin 6) : Fin angles.card :=
    ⟨i.val, by rw [hcard]; exact i.isLt⟩
  let φ : Fin 6 → ℝ := fun i => order (ix i)
  have hmono : StrictMono φ := by
    intro i j hij
    exact order.strictMono (show ix i < ix j by simpa [ix] using hij)
  have hmem (i : Fin 6) : φ i ∈ angles :=
    Finset.orderEmbOfFin_mem angles rfl (ix i)
  let src (i : Fin 6) : Fin 6 :=
    Classical.choose (Finset.mem_image.mp (hmem i))
  have harg (i : Fin 6) : polarArg (q (src i)) = φ i :=
    (Classical.choose_spec (Finset.mem_image.mp (hmem i))).2
  have hsrc : Function.Injective src := by
    intro i j h
    apply hmono.injective
    calc
      φ i = polarArg (q (src i)) := (harg i).symm
      _ = polarArg (q (src j)) := by rw [h]
      _ = φ j := harg j
  let sorted : Fin 6 → Plane := fun i => q (src i)
  have hfirst : -Real.pi < φ 0 := by
    rw [← harg 0]
    exact (polarArg_range (q (src 0))).1
  have hlast : φ 5 ≤ Real.pi := by
    rw [← harg 5]
    exact (polarArg_range (q (src 5))).2
  have hgap (i : Fin 6) : Real.pi / 3 < distinctSixGap φ i := by
    have hi : i ≠ i + 1 := by fin_cases i <;> decide
    have hcos := open_two_pair_cos_lt_half (sorted i) (sorted (i + 1))
      (hsmall (src i)) (hsmall (src (i + 1)))
      (hsep (src i) (src (i + 1)) (hsrc.ne hi))
    rw [distinctSixGap_cos_lift sorted φ harg i] at hcos
    have hg0 : 0 ≤ distinctSixGap φ i := by
      by_cases hi5 : i = 5
      · subst i
        simp only [distinctSixGap, ↓reduceIte]
        linarith
      · have hlt : i < i + 1 := by fin_cases i <;> simp_all
        have hφ := hmono hlt
        simp only [distinctSixGap, hi5, ↓reduceIte]
        linarith
    by_contra hnot
    have hg : distinctSixGap φ i ≤ Real.pi / 3 := le_of_not_gt hnot
    have hmonoCos := Real.cos_le_cos_of_nonneg_of_le_pi hg0
      (by nlinarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) hg
    rw [Real.cos_pi_div_three] at hmonoCos
    linarith
  have hsum : (∑ i : Fin 6, Real.pi / 3) <
      ∑ i : Fin 6, distinctSixGap φ i := by
    exact Finset.sum_lt_sum (fun i _ => (hgap i).le)
      ⟨0, Finset.mem_univ 0, hgap 0⟩
  rw [distinctSixGap_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

end CP15
