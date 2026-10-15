import CP15.M2EightAngle

namespace CP15

private noncomputable def eightGap (φ : Fin 8 → ℝ) (i : Fin 8) : ℝ :=
  if i = 7 then φ 0 + 2 * Real.pi - φ 7 else φ (i + 1) - φ i

private theorem eightGap_sum (φ : Fin 8 → ℝ) :
    (∑ i : Fin 8, eightGap φ i) = 2 * Real.pi := by
  rw [Fin.sum_univ_eight]
  simp [eightGap]

private theorem eightGap_nonneg (φ : Fin 8 → ℝ)
    (hmono : StrictMono φ)
    (hfirst : -Real.pi < φ 0) (hlast : φ 7 ≤ Real.pi)
    (i : Fin 8) : 0 ≤ eightGap φ i := by
  by_cases hi : i = 7
  · subst i
    simp [eightGap]
    linarith
  · have hlt : i < i + 1 := by
      fin_cases i <;> simp_all
    have hφ := hmono hlt
    simp [eightGap, hi]
    linarith

private theorem eightGap_cos_lift
    (q : Fin 8 → Plane) (src : Fin 8 → Fin 8)
    (φ : Fin 8 → ℝ)
    (harg : ∀ i, polarArg (q (src i)) = φ i)
    (i : Fin 8) :
    Real.cos (polarArg (q (src i)) -
      polarArg (q (src (i + 1)))) = Real.cos (eightGap φ i) := by
  by_cases hi : i = 7
  · subst i
    simp [eightGap, harg]
    have heq : φ 7 - φ 0 = 2 * Real.pi -
        (φ 0 + 2 * Real.pi - φ 7) := by ring
    rw [heq, Real.cos_two_pi_sub]
  · rw [harg i, harg (i + 1)]
    simp only [eightGap, hi, ↓reduceIte]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

/-- Eight separated inner centers with two low and six high radii cannot
fit around the origin. All cyclic gaps, including the closing one, are
charged; the finite color bound is kernel reduced. -/
theorem eight_inner_directions_impossible
    (q : Fin 8 → Plane) (hsep : Separated q 2)
    (src : Fin 8 → Fin 8) (hsrc : Function.Injective src)
    (φ : Fin 8 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q (src i)) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 7 ≤ Real.pi)
    (color : Fin 8 → Bool)
    (hcount : (Finset.univ.filter (fun i => color i)).card = 2)
    (hrad : ∀ i, if color i then
      (699 / 1000 : ℝ) ≤ ‖q (src i)‖ ∧
        ‖q (src i)‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q (src i)‖ ∧
        ‖q (src i)‖ ≤ 14909 / 6250) : False := by
  have hcost (i : Fin 8) :
      ((eightAngleWeight color i : ℚ) : ℝ) ≤ eightGap φ i := by
    let j := i + 1
    have hij : i ≠ j := by
      dsimp [j]
      fin_cases i <;> decide
    have hsepij : 2 ≤ dist (q (src i)) (q (src j)) :=
      hsep (src i) (src j) (hsrc.ne hij)
    have hgap0 := eightGap_nonneg φ hmono hfirst hlast i
    have hcos := eightGap_cos_lift q src φ harg i
    have hcosrev : Real.cos (polarArg (q (src j)) -
        polarArg (q (src i))) = Real.cos (eightGap φ i) := by
      have heq : polarArg (q (src j)) - polarArg (q (src i)) =
          -(polarArg (q (src i)) - polarArg (q (src j))) := by ring
      rw [heq, Real.cos_neg]
      exact hcos
    by_cases hgpi : eightGap φ i ≤ Real.pi
    · by_cases hci : color i = true
      · by_cases hcj : color j = true
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := low_low_angle_gt_pi_div_two
            (q (src i)) (q (src j)) (eightGap φ i)
            (by linarith [hi.1]) (by linarith [hj.1])
            hi.2 hj.2 hsepij hcos hgap0 hgpi
          simp [eightAngleWeight, hci, hcj, j]
          linarith [Real.pi_gt_three]
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := m2_low_high_angle_gt_three_fourths
            (q (src i)) (q (src j)) (eightGap φ i)
            hi.1 hi.2 hj.1 hj.2 hsepij hcos hgap0 hgpi
          simp [eightAngleWeight, hci, hcj, j]
          linarith
      · by_cases hcj : color j = true
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := m2_low_high_angle_gt_three_fourths
            (q (src j)) (q (src i)) (eightGap φ i)
            hj.1 hj.2 hi.1 hi.2 (by simpa [dist_comm] using hsepij)
            hcosrev hgap0 hgpi
          simp [eightAngleWeight, hci, hcj, j]
          linarith
        · have hi := by simpa [hci] using hrad i
          have hj := by simpa [hcj] using hrad j
          have ha := high_high_angle_gt_171_div_200
            (q (src i)) (q (src j)) (eightGap φ i)
            hi.1 hi.2 hj.1 hj.2 hsepij hcos hgap0 hgpi
          simp [eightAngleWeight, hci, hcj, j]
          linarith
    · have hglarge : Real.pi < eightGap φ i := lt_of_not_ge hgpi
      have hweight : (eightAngleWeight color i : ℝ) ≤ 3 / 2 := by
        unfold eightAngleWeight
        split_ifs <;> norm_num
      linarith [Real.pi_gt_three]
  have hweightSum : (321 / 50 : ℝ) ≤
      ∑ i : Fin 8, ((eightAngleWeight color i : ℚ) : ℝ) := by
    have hq := eightAngleWeight_sum_ge color hcount
    have hbase : ((321 / 50 : ℚ) : ℝ) ≤
        ((∑ i : Fin 8, eightAngleWeight color i : ℚ) : ℝ) := by
      exact (Rat.cast_le).2 hq
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hbase
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hcost i)
  rw [eightGap_sum] at hsum
  have hpi : Real.pi < (3141593 / 1000000 : ℝ) := by
    linarith [Real.pi_lt_d6]
  linarith

/-- The label-free geometric form. Labels `0,1` are low radius and
`2,...,7` are high radius. The proof sorts the actual polar directions. -/
theorem eight_low_high_centers_impossible
    (q : Fin 8 → Plane) (hsep : Separated q 2)
    (hrad : ∀ i, if i.val < 2 then
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 14909 / 6250) : False := by
  classical
  have hrlo (i : Fin 8) : (699 / 1000 : ℝ) ≤ ‖q i‖ := by
    by_cases h : i.val < 2
    · have hi := hrad i
      simp [h] at hi
      exact hi.1
    · have hi := hrad i
      simp [h] at hi
      linarith [hi.1]
  have hrhi (i : Fin 8) : ‖q i‖ ≤ 14909 / 6250 := by
    by_cases h : i.val < 2
    · have hi := hrad i
      simp [h] at hi
      linarith [hi.2]
    · have hi := hrad i
      simp [h] at hi
      exact hi.2
  have hpolar := eight_polarArg_injective q hsep hrlo hrhi
  let angles : Finset ℝ :=
    Finset.univ.image (fun i : Fin 8 => polarArg (q i))
  have hcard : angles.card = 8 := by
    dsimp [angles]
    simpa using Finset.card_image_of_injective Finset.univ hpolar
  let order := angles.orderEmbOfFin rfl
  let ix (i : Fin 8) : Fin angles.card :=
    ⟨i.val, by rw [hcard]; exact i.isLt⟩
  let φ : Fin 8 → ℝ := fun i => order (ix i)
  have hmono : StrictMono φ := by
    intro i j hij
    exact order.strictMono (show ix i < ix j by simpa [ix] using hij)
  have hmem (i : Fin 8) : φ i ∈ angles :=
    Finset.orderEmbOfFin_mem angles rfl (ix i)
  let src (i : Fin 8) : Fin 8 :=
    Classical.choose (Finset.mem_image.mp (hmem i))
  have harg (i : Fin 8) : polarArg (q (src i)) = φ i := by
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
  let color : Fin 8 → Bool := fun i => decide ((src i).val < 2)
  have hcount : (Finset.univ.filter (fun i => color i)).card = 2 := by
    have himage :
        (Finset.univ.filter (fun i => color i)).image src =
          Finset.univ.filter (fun i : Fin 8 => i.val < 2) := by
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
    have htwo : (Finset.univ.filter (fun i : Fin 8 => i.val < 2)).card = 2 := by
      decide
    omega
  have hfirst : -Real.pi < φ 0 := by
    rw [← harg 0]
    exact (polarArg_range (q (src 0))).1
  have hlast : φ 7 ≤ Real.pi := by
    rw [← harg 7]
    exact (polarArg_range (q (src 7))).2
  have hradSorted (i : Fin 8) : if color i then
      (699 / 1000 : ℝ) ≤ ‖q (src i)‖ ∧
        ‖q (src i)‖ ≤ 1301 / 1000
      else (7 / 5 : ℝ) ≤ ‖q (src i)‖ ∧
        ‖q (src i)‖ ≤ 14909 / 6250 := by
    simpa [color] using hrad (src i)
  exact eight_inner_directions_impossible q hsep src hsrc φ hmono harg
    hfirst hlast color hcount hradSorted

end CP15
