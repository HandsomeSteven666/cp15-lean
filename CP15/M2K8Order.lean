import CP15.M2K8Budget

namespace CP15

private noncomputable def twoLowGap (φ : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  if i = 6 then φ 0 + 2 * Real.pi - φ 6 else φ (i + 1) - φ i

private theorem twoLowGap_sum (φ : Fin 7 → ℝ) :
    (∑ i : Fin 7, twoLowGap φ i) = 2 * Real.pi := by
  rw [Fin.sum_univ_seven]
  simp [twoLowGap]

private theorem twoLowGap_nonneg (φ : Fin 7 → ℝ)
    (hmono : StrictMono φ)
    (hfirst : -Real.pi < φ 0) (hlast : φ 6 ≤ Real.pi)
    (i : Fin 7) : 0 ≤ twoLowGap φ i := by
  by_cases hi : i = 6
  · subst i
    simp [twoLowGap]
    linarith
  · have hlt : i < i + 1 := by
      fin_cases i <;> simp_all
    have hφ := hmono hlt
    simp [twoLowGap, hi]
    linarith

private theorem twoLowGap_cos_lift
    (q : Fin 7 → Plane) (φ : Fin 7 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (i : Fin 7) :
    Real.cos (polarArg (q i) - polarArg (q (i + 1))) =
      Real.cos (twoLowGap φ i) := by
  by_cases hi : i = 6
  · subst i
    simp [twoLowGap, harg]
    have heq : φ 6 - φ 0 = 2 * Real.pi -
        (φ 0 + 2 * Real.pi - φ 6) := by ring
    rw [heq, Real.cos_two_pi_sub]
  · rw [harg i, harg (i + 1)]
    simp only [twoLowGap, hi, ↓reduceIte]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

/-- The radius-sensitive seven-direction contradiction at `K = 8`.
The low centers may occupy arbitrary two distinct positions in the polar
order, and the actual two radii select one of eight exact rational cells. -/
theorem seven_two_low_ordered_impossible
    (q : Fin 7 → Plane) (hsep : Separated q 2)
    (φ : Fin 7 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 6 ≤ Real.pi)
    (pos0 pos1 : Fin 7) (hne : pos0 ≠ pos1)
    (k : Fin 8)
    (hlo0 : (m2CellA k : ℝ) ≤ ‖q pos0‖ ∧
      ‖q pos0‖ ≤ 1301 / 1000)
    (hlo1 : (m2CellA ⟨7 - k.val, by omega⟩ : ℝ) ≤ ‖q pos1‖ ∧
      ‖q pos1‖ ≤ 1301 / 1000)
    (hhigh : ∀ i, i ≠ pos0 → i ≠ pos1 →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 14909 / 6250) : False := by
  let k1 : Fin 8 := ⟨7 - k.val, by omega⟩
  let q0 : ℝ := m2CellQ k
  let q1 : ℝ := m2CellQ k1
  have hcell := m2_cell_rational_conditions k
  have hcell1 := m2_cell_rational_conditions k1
  have hqsum : (1851 / 1000 : ℝ) ≤ q0 + q1 := by
    dsimp [q0, q1, k1]
    fin_cases k <;> norm_num [m2CellQ]
  have hcost (i : Fin 7) :
      sevenTwoLowWeight pos0 pos1 q0 q1 i ≤ twoLowGap φ i := by
    let j := i + 1
    have hij : i ≠ j := by
      dsimp [j]
      fin_cases i <;> decide
    have hsepij := hsep i j hij
    have hg0 := twoLowGap_nonneg φ hmono hfirst hlast i
    have hcos := twoLowGap_cos_lift q φ harg i
    have hcosrev : Real.cos (polarArg (q j) - polarArg (q i)) =
        Real.cos (twoLowGap φ i) := by
      have heq : polarArg (q j) - polarArg (q i) =
          -(polarArg (q i) - polarArg (q j)) := by ring
      rw [heq, Real.cos_neg]
      exact hcos
    by_cases hgpi : twoLowGap φ i ≤ Real.pi
    · by_cases hi0 : i = pos0
      · by_cases hj1 : j = pos1
        · have hj1' : i + 1 = pos1 := by simpa [j] using hj1
          have hj1pos0 : pos0 + 1 = pos1 := by simpa [hi0] using hj1'
          have hsep' : 2 ≤ dist (q pos0) (q pos1) := by
            simpa [j, hi0, hj1pos0] using hsepij
          have hcos' : Real.cos (polarArg (q pos0) -
              polarArg (q pos1)) = Real.cos (twoLowGap φ i) := by
            simpa [hi0, hj1pos0] using hcos
          have ha := low_low_angle_gt_pi_div_two
            (q pos0) (q pos1) (twoLowGap φ i)
            (by linarith [hlo0.1, hcell.1])
            (by linarith [hlo1.1, hcell1.1])
            hlo0.2 hlo1.2 hsep' hcos' hg0 hgpi
          have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i = 3 / 2 := by
            simp [sevenTwoLowWeight, hi0, hj1pos0]
          rw [hweight]
          linarith [Real.pi_gt_three]
        · have hj0 : j ≠ pos0 := by
            intro h
            exact hij (hi0.trans h.symm)
          have hh := hhigh j hj0 hj1
          have ha := m2_low_high_angle_gt_cell k
            (q i) (q j) (twoLowGap φ i)
            (hi0 ▸ hlo0.1) (hi0 ▸ hlo0.2)
            hh.1 hh.2 hsepij hcos hg0 hgpi
          have hj1' : i + 1 ≠ pos1 := by simpa [j] using hj1
          have hj1pos0 : pos0 + 1 ≠ pos1 := by simpa [hi0] using hj1'
          have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i = q0 := by
            simp [sevenTwoLowWeight, hi0, hj1pos0]
          rw [hweight]
          exact ha.le
      · by_cases hi1 : i = pos1
        · by_cases hj0 : j = pos0
          · have ha := low_low_angle_gt_pi_div_two
              (q i) (q j) (twoLowGap φ i)
              (by rw [hi1]; linarith [hlo1.1, hcell1.1])
              (by rw [hj0]; linarith [hlo0.1, hcell.1])
              (by simpa [hi1] using hlo1.2)
              (by simpa [hj0] using hlo0.2)
              hsepij hcos hg0 hgpi
            have hj0' : i + 1 = pos0 := by simpa [j] using hj0
            have hj0pos1 : pos1 + 1 = pos0 := by simpa [hi1] using hj0'
            have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i = 3 / 2 := by
              simp [sevenTwoLowWeight, hi1, hne.symm, hj0pos1]
            rw [hweight]
            linarith [Real.pi_gt_three]
          · have hj1 : j ≠ pos1 := by
              intro h
              exact hij (hi1.trans h.symm)
            have hh := hhigh j hj0 hj1
            have ha := m2_low_high_angle_gt_cell k1
              (q i) (q j) (twoLowGap φ i)
              (by simpa [hi1, k1] using hlo1.1)
              (by simpa [hi1] using hlo1.2)
              hh.1 hh.2 hsepij hcos hg0 hgpi
            have hj0' : i + 1 ≠ pos0 := by simpa [j] using hj0
            have hj0pos1 : pos1 + 1 ≠ pos0 := by simpa [hi1] using hj0'
            have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i = q1 := by
              simp [sevenTwoLowWeight, hi1, hne.symm, hj0pos1]
            rw [hweight]
            exact ha.le
        · have hh := hhigh i hi0 hi1
          by_cases hj0 : j = pos0
          · have ha := m2_low_high_angle_gt_cell k
              (q j) (q i) (twoLowGap φ i)
              (by simpa [hj0] using hlo0.1)
              (by simpa [hj0] using hlo0.2)
              hh.1 hh.2 (by simpa [dist_comm] using hsepij)
              hcosrev hg0 hgpi
            have hj0' : i + 1 = pos0 := by simpa [j] using hj0
            have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i = q0 := by
              simp [sevenTwoLowWeight, hi0, hi1, hj0']
            rw [hweight]
            exact ha.le
          · by_cases hj1 : j = pos1
            · have ha := m2_low_high_angle_gt_cell k1
                (q j) (q i) (twoLowGap φ i)
                (by simpa [hj1, k1] using hlo1.1)
                (by simpa [hj1] using hlo1.2)
                hh.1 hh.2 (by simpa [dist_comm] using hsepij)
                hcosrev hg0 hgpi
              have hj0' : i + 1 ≠ pos0 := by simpa [j] using hj0
              have hj1' : i + 1 = pos1 := by simpa [j] using hj1
              have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i = q1 := by
                simp [sevenTwoLowWeight, hi0, hi1, hj0', hj1', hne.symm]
              rw [hweight]
              exact ha.le
            · have hhh := hhigh j hj0 hj1
              have ha := high_high_angle_gt_171_div_200
                (q i) (q j) (twoLowGap φ i)
                hh.1 hh.2 hhh.1 hhh.2 hsepij hcos hg0 hgpi
              have hbetter : (431 / 500 : ℝ) < twoLowGap φ i := by
                have hcosbound : (65 / 100 : ℝ) < Real.cos (431 / 500 : ℝ) := by
                  have h := cos_lower_from_sin_cubic (431 / 500 : ℝ)
                    (by norm_num) (by norm_num)
                  have hr : (65 / 100 : ℝ) <
                      1 - 2 * sinCubicUpper ((431 / 500 : ℝ) / 2) ^ 2 := by
                    norm_num [sinCubicUpper]
                  linarith
                exact polar_pair_angle_gt_of_poly (q i) (q j)
                  (twoLowGap φ i) (65 / 100) (431 / 500)
                  (by linarith [hh.1]) (by linarith [hhh.1])
                  hsepij
                  (high_high_pair_cos_poly_lt ‖q i‖ ‖q j‖
                    hh.1 hh.2 hhh.1 hhh.2)
                  hcos hg0 hgpi (by norm_num)
                  (by linarith [Real.pi_gt_three]) hcosbound
              have hj0' : i + 1 ≠ pos0 := by simpa [j] using hj0
              have hj1' : i + 1 ≠ pos1 := by simpa [j] using hj1
              have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i = 431 / 500 := by
                simp [sevenTwoLowWeight, hi0, hi1, hj0', hj1']
              rw [hweight]
              exact hbetter.le
    · have hglarge : Real.pi < twoLowGap φ i := lt_of_not_ge hgpi
      have hweight : sevenTwoLowWeight pos0 pos1 q0 q1 i ≤ 3 / 2 := by
        have hq0 : q0 ≤ 1 := by dsimp [q0]; exact hcell.2.2.2.2.2.2
        have hq1 : q1 ≤ 1 := by dsimp [q1]; exact hcell1.2.2.2.2.2.2
        unfold sevenTwoLowWeight
        split_ifs <;> norm_num <;> linarith
      linarith [Real.pi_gt_three]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hcost i)
  rw [twoLowGap_sum] at hsum
  have hbudget := sevenTwoLowWeight_sum_ge q0 q1
    (by dsimp [q0]; exact hcell.2.2.2.2.2.1)
    (by dsimp [q1]; exact hcell1.2.2.2.2.2.1)
    hqsum pos0 pos1 hne
  have hpi : Real.pi < (3141593 / 1000000 : ℝ) := by
    linarith [Real.pi_lt_d6]
  linarith

/-- Seven actual centers, two with low and five with high radial bounds,
cannot be pairwise separated. The proof builds and counts the complete
sorted polar order rather than assuming a convex inner polygon. -/
theorem seven_two_low_centers_impossible
    (q : Fin 7 → Plane) (hsep : Separated q 2)
    (hrad : ∀ i, if i.val < 2 then
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 14909 / 6250) : False := by
  classical
  have hrlo (i : Fin 7) : (699 / 1000 : ℝ) ≤ ‖q i‖ := by
    by_cases h : i.val < 2
    · have hi := hrad i
      simp [h] at hi
      exact hi.1
    · have hi := hrad i
      simp [h] at hi
      linarith [hi.1]
  have hrhi (i : Fin 7) : ‖q i‖ ≤ 14909 / 6250 := by
    by_cases h : i.val < 2
    · have hi := hrad i
      simp [h] at hi
      linarith [hi.2]
    · have hi := hrad i
      simp [h] at hi
      exact hi.2
  have hpolar : Function.Injective (fun i => polarArg (q i)) := by
    intro i j harg
    by_contra hij
    have hd := hsep i j hij
    have hd2 : 4 ≤ dist (q i) (q j) ^ 2 := by
      nlinarith [dist_nonneg (x := q i) (y := q j)]
    rw [dist_eq_norm, norm_sub_sq_real] at hd2
    have hdot := polar_inner (q i) (q j)
    change polarArg (q i) = polarArg (q j) at harg
    rw [harg, sub_self, Real.cos_zero] at hdot
    nlinarith [hrlo i, hrlo j, hrhi i, hrhi j]
  let angles : Finset ℝ :=
    Finset.univ.image (fun i : Fin 7 => polarArg (q i))
  have hcard : angles.card = 7 := by
    dsimp [angles]
    simpa using Finset.card_image_of_injective Finset.univ hpolar
  let order := angles.orderEmbOfFin rfl
  let ix (i : Fin 7) : Fin angles.card :=
    ⟨i.val, by rw [hcard]; exact i.isLt⟩
  let φ : Fin 7 → ℝ := fun i => order (ix i)
  have hmono : StrictMono φ := by
    intro i j hij
    exact order.strictMono (show ix i < ix j by simpa [ix] using hij)
  have hmem (i : Fin 7) : φ i ∈ angles :=
    Finset.orderEmbOfFin_mem angles rfl (ix i)
  let src (i : Fin 7) : Fin 7 :=
    Classical.choose (Finset.mem_image.mp (hmem i))
  have harg (i : Fin 7) : polarArg (q (src i)) = φ i := by
    exact (Classical.choose_spec (Finset.mem_image.mp (hmem i))).2
  have hsrc : Function.Injective src := by
    intro i j h
    apply hmono.injective
    calc
      φ i = polarArg (q (src i)) := (harg i).symm
      _ = polarArg (q (src j)) := by rw [h]
      _ = φ j := harg j
  have hsurj : Function.Surjective src :=
    Finite.surjective_of_injective hsrc
  obtain ⟨pos0, hpos0⟩ := hsurj 0
  obtain ⟨pos1, hpos1⟩ := hsurj 1
  have hne : pos0 ≠ pos1 := by
    intro h
    have he : (0 : Fin 7) = 1 := by
      rw [← hpos0, ← hpos1, h]
    exact (by decide : (0 : Fin 7) ≠ 1) he
  let sorted : Fin 7 → Plane := fun i => q (src i)
  have hsepsorted : Separated sorted 2 := by
    intro i j hij
    exact hsep (src i) (src j) (hsrc.ne hij)
  have hrad0 : (699 / 1000 : ℝ) ≤ ‖sorted pos0‖ ∧
      ‖sorted pos0‖ ≤ 1301 / 1000 := by
    simpa [sorted, hpos0] using hrad 0
  have hrad1 : (699 / 1000 : ℝ) ≤ ‖sorted pos1‖ ∧
      ‖sorted pos1‖ ≤ 1301 / 1000 := by
    simpa [sorted, hpos1] using hrad 1
  have hpair : 2 ≤ ‖sorted pos0‖ + ‖sorted pos1‖ := by
    have hs := hsepsorted pos0 pos1 hne
    have ht := norm_sub_le (sorted pos0) (sorted pos1)
    rw [dist_eq_norm] at hs
    linarith
  obtain ⟨k, hk0, hk1, hqsum⟩ :=
    m2_pair_eight_cell_cover ‖sorted pos0‖ ‖sorted pos1‖
      hrad0.1 hrad0.2 hpair
  have hhigh (i : Fin 7) (hi0 : i ≠ pos0) (hi1 : i ≠ pos1) :
      (7 / 5 : ℝ) ≤ ‖sorted i‖ ∧
        ‖sorted i‖ ≤ 14909 / 6250 := by
    have hnot0 : src i ≠ 0 := by
      intro h
      exact hi0 (hsrc (h.trans hpos0.symm))
    have hnot1 : src i ≠ 1 := by
      intro h
      exact hi1 (hsrc (h.trans hpos1.symm))
    have hge : ¬(src i).val < 2 := by
      intro hlt
      have hc : (src i).val = 0 ∨ (src i).val = 1 := by omega
      rcases hc with hc | hc
      · exact hnot0 (Fin.ext hc)
      · exact hnot1 (Fin.ext hc)
    simpa [sorted, hge] using hrad (src i)
  have hfirst : -Real.pi < φ 0 := by
    rw [← harg 0]
    exact (polarArg_range (q (src 0))).1
  have hlast : φ 6 ≤ Real.pi := by
    rw [← harg 6]
    exact (polarArg_range (q (src 6))).2
  exact seven_two_low_ordered_impossible sorted hsepsorted φ hmono
    harg hfirst hlast pos0 pos1 hne k
    ⟨hk0, hrad0.2⟩ ⟨hk1, hrad1.2⟩ hhigh

end CP15
