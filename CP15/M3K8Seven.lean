import CP15.SevenAngleBudget

namespace CP15

private noncomputable def sevenGap (φ : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  if i = 6 then φ 0 + 2 * Real.pi - φ 6 else φ (i + 1) - φ i

private theorem sevenGap_sum (φ : Fin 7 → ℝ) :
    (∑ i : Fin 7, sevenGap φ i) = 2 * Real.pi := by
  rw [Fin.sum_univ_seven]
  simp [sevenGap]

private theorem sevenGap_nonneg (φ : Fin 7 → ℝ)
    (hmono : StrictMono φ)
    (hfirst : -Real.pi < φ 0) (hlast : φ 6 ≤ Real.pi)
    (i : Fin 7) : 0 ≤ sevenGap φ i := by
  by_cases hi : i = 6
  · subst i
    simp [sevenGap]
    linarith
  · have hlt : i < i + 1 := by
      fin_cases i <;> simp_all
    have hφ := hmono hlt
    simp [sevenGap, hi]
    linarith

private theorem sevenGap_cos_lift
    (q : Fin 7 → Plane) (src : Fin 7 → Fin 7)
    (φ : Fin 7 → ℝ)
    (harg : ∀ i, polarArg (q (src i)) = φ i)
    (i : Fin 7) :
    Real.cos (polarArg (q (src i)) -
      polarArg (q (src (i + 1)))) = Real.cos (sevenGap φ i) := by
  by_cases hi : i = 6
  · subst i
    simp [sevenGap, harg]
    have heq : φ 6 - φ 0 = 2 * Real.pi -
        (φ 0 + 2 * Real.pi - φ 6) := by ring
    rw [heq, Real.cos_two_pi_sub]
  · rw [harg i, harg (i + 1)]
    simp only [sevenGap, hi, ↓reduceIte]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

/-- No ordered seven-center system can contain three low-radius and four
high-radius centers under the checked radial ranges. The finite color-word
accounting is exact; every wrap-around gap is included. -/
theorem seven_inner_directions_impossible
    (q : Fin 7 → Plane) (hsep : Separated q 2)
    (src : Fin 7 → Fin 7) (hsrc : Function.Injective src)
    (φ : Fin 7 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q (src i)) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 6 ≤ Real.pi)
    (color : Fin 7 → Bool)
    (hcount : (Finset.univ.filter (fun i => color i)).card = 3)
    (hrad : ∀ i, if color i then
      (4 / 5 : ℝ) ≤ ‖q (src i)‖ ∧ ‖q (src i)‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q (src i)‖ ∧
        ‖q (src i)‖ ≤ 14909 / 6250) : False := by
  have hcost (i : Fin 7) :
      ((sevenAngleWeight color i : ℚ) : ℝ) ≤ sevenGap φ i := by
    let j := i + 1
    have hij : i ≠ j := by
      dsimp [j]
      fin_cases i <;> decide
    have hsepij : 2 ≤ dist (q (src i)) (q (src j)) :=
      hsep (src i) (src j) (hsrc.ne hij)
    have hgap0 := sevenGap_nonneg φ hmono hfirst hlast i
    have hcos := sevenGap_cos_lift q src φ harg i
    have hcosrev : Real.cos (polarArg (q (src j)) -
        polarArg (q (src i))) = Real.cos (sevenGap φ i) := by
      have heq : polarArg (q (src j)) - polarArg (q (src i)) =
          -(polarArg (q (src i)) - polarArg (q (src j))) := by ring
      rw [heq, Real.cos_neg]
      exact hcos
    by_cases hgpi : sevenGap φ i ≤ Real.pi
    · by_cases hci : color i = true
      · by_cases hcj : color j = true
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := low_low_angle_gt_pi_div_two
            (q (src i)) (q (src j)) (sevenGap φ i)
            (by linarith [hi.1]) (by linarith [hj.1])
            hi.2 hj.2 hsepij hcos hgap0 hgpi
          simp [sevenAngleWeight, hci, hcj, j]
          linarith [Real.pi_gt_three]
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := low_high_angle_gt_181_div_200
            (q (src i)) (q (src j)) (sevenGap φ i)
            hi.1 hi.2 hj.1 hj.2 hsepij hcos hgap0 hgpi
          simp [sevenAngleWeight, hci, hcj, j]
          linarith
      · by_cases hcj : color j = true
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := low_high_angle_gt_181_div_200
            (q (src j)) (q (src i)) (sevenGap φ i)
            hj.1 hj.2 hi.1 hi.2 (by simpa [dist_comm] using hsepij)
            hcosrev hgap0 hgpi
          simp [sevenAngleWeight, hci, hcj, j]
          linarith
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := high_high_angle_gt_171_div_200
            (q (src i)) (q (src j)) (sevenGap φ i)
            hi.1 hi.2 hj.1 hj.2 hsepij hcos hgap0 hgpi
          simp [sevenAngleWeight, hci, hcj, j]
          linarith
    · have hglarge : Real.pi < sevenGap φ i := lt_of_not_ge hgpi
      have hweight : (sevenAngleWeight color i : ℝ) ≤ 3 / 2 := by
        unfold sevenAngleWeight
        split_ifs <;> norm_num
      linarith [Real.pi_gt_three]
  have hweightSum : (1257 / 200 : ℝ) ≤
      ∑ i : Fin 7, ((sevenAngleWeight color i : ℚ) : ℝ) := by
    have hq := sevenAngleWeight_sum_ge color hcount
    have hbase : ((1257 / 200 : ℚ) : ℝ) ≤
        ((∑ i : Fin 7, sevenAngleWeight color i : ℚ) : ℝ) := by
      exact (Rat.cast_le).2 hq
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hbase
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hcost i)
  rw [sevenGap_sum] at hsum
  have hpi : Real.pi < (3141593 / 1000000 : ℝ) := by
    linarith [Real.pi_lt_d6]
  linarith

/-- The seven-center geometric form. Labels `0,1,2` have the low radial
range; labels `3,4,5,6` have the high range. The proof constructs the
complete sorted polar order and transfers the three-color count through a
bijection, including the cyclic closing gap. -/
theorem seven_low_high_centers_impossible
    (q : Fin 7 → Plane) (hsep : Separated q 2)
    (hrad : ∀ i, if i.val < 3 then
      (4 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 14909 / 6250) : False := by
  classical
  have hrlo (i : Fin 7) : (4 / 5 : ℝ) ≤ ‖q i‖ := by
    by_cases h : i.val < 3
    · have hi := hrad i
      simp [h] at hi
      exact hi.1
    · have hi := hrad i
      simp [h] at hi
      linarith [hi.1]
  have hrhi (i : Fin 7) : ‖q i‖ ≤ 14909 / 6250 := by
    by_cases h : i.val < 3
    · have hi := hrad i
      simp [h] at hi
      linarith [hi.2]
    · have hi := hrad i
      simp [h] at hi
      exact hi.2
  have hpolar := seven_polarArg_injective q hsep hrlo hrhi
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
  let color : Fin 7 → Bool := fun i => decide ((src i).val < 3)
  have hcount : (Finset.univ.filter (fun i => color i)).card = 3 := by
    have himage :
        (Finset.univ.filter (fun i => color i)).image src =
          Finset.univ.filter (fun i : Fin 7 => i.val < 3) := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        simpa [color] using hj
      · intro hi
        obtain ⟨j, rfl⟩ := hsurj i
        apply Finset.mem_image.mpr
        exact ⟨j, by simpa [color] using hi, rfl⟩
    have hcardimage := Finset.card_image_of_injective
      (Finset.univ.filter (fun i => color i)) hsrc
    rw [himage] at hcardimage
    have hthree : (Finset.univ.filter (fun i : Fin 7 => i.val < 3)).card = 3 := by
      decide
    omega
  have hfirst : -Real.pi < φ 0 := by
    rw [← harg 0]
    exact (polarArg_range (q (src 0))).1
  have hlast : φ 6 ≤ Real.pi := by
    rw [← harg 6]
    exact (polarArg_range (q (src 6))).2
  have hradSorted (i : Fin 7) : if color i then
      (4 / 5 : ℝ) ≤ ‖q (src i)‖ ∧ ‖q (src i)‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q (src i)‖ ∧
        ‖q (src i)‖ ≤ 14909 / 6250 := by
    simpa [color] using hrad (src i)
  exact seven_inner_directions_impossible q hsep src hsrc φ hmono harg
    hfirst hlast color hcount hradSorted

end CP15
