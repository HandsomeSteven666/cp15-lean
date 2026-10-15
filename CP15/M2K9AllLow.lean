import CP15.M2K9PairCorners
import CP15.M2K9ClassWords

namespace CP15

private noncomputable def sixGap (φ : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  if i = 5 then φ 0 + 2 * Real.pi - φ 5 else φ (i + 1) - φ i

private theorem sixGap_sum (φ : Fin 6 → ℝ) :
    (∑ i : Fin 6, sixGap φ i) = 2 * Real.pi := by
  rw [Fin.sum_univ_six]
  simp [sixGap]

private theorem sixGap_nonneg (φ : Fin 6 → ℝ)
    (hmono : StrictMono φ)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (i : Fin 6) : 0 ≤ sixGap φ i := by
  by_cases hi : i = 5
  · subst i
    simp [sixGap]
    linarith
  · have hlt : i < i + 1 := by
      fin_cases i <;> simp_all
    have hφ := hmono hlt
    simp [sixGap, hi]
    linarith

private theorem sixGap_cos_lift
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (i : Fin 6) :
    Real.cos (polarArg (q i) - polarArg (q (i + 1))) =
      Real.cos (sixGap φ i) := by
  by_cases hi : i = 5
  · subst i
    simp [sixGap, harg]
    have heq : φ 5 - φ 0 =
        2 * Real.pi - (φ 0 + 2 * Real.pi - φ 5) := by ring
    rw [heq, Real.cos_two_pi_sub]
  · rw [harg i, harg (i + 1)]
    simp only [sixGap, hi, ↓reduceIte]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

private theorem shared_all_low_gap_cost
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L →
      (29 / 20 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (i : Fin 6) :
    ((sharedAllLowCost (w i) (w (i + 1)) : ℕ) : ℝ) *
      Real.pi / 1800 ≤ sixGap φ i ∧
    (w i = .A →
      ((sharedAllLowCost (w i) (w (i + 1)) : ℕ) : ℝ) *
        Real.pi / 1800 < sixGap φ i) := by
  let j := i + 1
  have hij : i ≠ j := by dsimp [j]; fin_cases i <;> decide
  have hsepij : 2 ≤ dist (q i) (q j) := hsep i j hij
  have hg0 := sixGap_nonneg φ hmono hfirst hlast i
  have hcos := sixGap_cos_lift q φ harg i
  have hcosrev :
      Real.cos (polarArg (q j) - polarArg (q i)) =
        Real.cos (sixGap φ i) := by
    have heq : polarArg (q j) - polarArg (q i) =
        -(polarArg (q i) - polarArg (q j)) := by ring
    rw [heq, Real.cos_neg]
    exact hcos
  by_cases hgpi : sixGap φ i ≤ Real.pi
  · cases hwi : w i <;> cases hwj : w j
    · have hi := hA i hwi
      have hj := hA j hwj
      have ha := shared_AA_angle_gt_99 (q i) (q j) (sixGap φ i)
        hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      constructor <;> linarith
    · have hi := hA i hwi
      have hj := hH j hwj
      have ha := shared_AH_angle_gt_49_2 (q i) (q j) (sixGap φ i)
        hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      constructor <;> linarith
    · have hi := hA i hwi
      have hj := hL j hwj
      have ha := shared_AL_angle_gt_70_8 (q i) (q j) (sixGap φ i)
        hi.1 hi.2 (by linarith [hj.1]) hj.2 hsepij hcos hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      constructor <;> linarith
    · have hi := hH i hwi
      have hj := hA j hwj
      have ha := shared_AH_angle_gt_49_2 (q j) (q i) (sixGap φ i)
        hj.1 hj.2 hi.1 hi.2 (by simpa [dist_comm] using hsepij)
        hcosrev hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      linarith
    · simp [sharedAllLowCost, hwi, hwj, j, hg0]
    · have hi := hH i hwi
      have hj := hL j hwj
      have ha := shared_HL_angle_gt_53 (q i) (q j) (sixGap φ i)
        hi.1 hi.2 (by linarith [hj.1]) hj.2 hsepij hcos hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      linarith
    · have hi := hL i hwi
      have hj := hA j hwj
      have ha := shared_AL_angle_gt_70_8 (q j) (q i) (sixGap φ i)
        hj.1 hj.2 (by linarith [hi.1]) hi.2 (by simpa [dist_comm] using hsepij)
        hcosrev hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      linarith
    · have hi := hL i hwi
      have hj := hH j hwj
      have ha := shared_HL_angle_gt_53 (q j) (q i) (sixGap φ i)
        hj.1 hj.2 (by linarith [hi.1]) hi.2 (by simpa [dist_comm] using hsepij)
        hcosrev hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      linarith
    · have hi := hL i hwi
      have hj := hL j hwj
      have ha := shared_LL_angle_ge_60 (q i) (q j) (sixGap φ i)
        (by linarith [hi.1]) hi.2 (by linarith [hj.1]) hj.2 hsepij hcos hg0 hgpi
      simp [sharedAllLowCost, hwi, hwj, j]
      linarith
  · have hglarge : Real.pi < sixGap φ i := lt_of_not_ge hgpi
    have hweight : sharedAllLowCost (w i) (w j) ≤ 990 := by
      cases w i <;> cases w j <;> norm_num [sharedAllLowCost]
    constructor
    · have hpi : 0 < Real.pi := Real.pi_pos
      exact le_of_lt (by
        have : ((sharedAllLowCost (w i) (w j) : ℕ) : ℝ) ≤ 990 :=
          Nat.cast_le.mpr hweight
        nlinarith)
    · intro _
      have : ((sharedAllLowCost (w i) (w j) : ℕ) : ℝ) ≤ 990 :=
        Nat.cast_le.mpr hweight
      nlinarith [Real.pi_pos]

/-- Once an actual ordered six-center word has the displayed radius
classes, all-low is impossible. Every cyclic gap, including wrap-around,
is charged, and strictness is taken from an `A`-incident edge. -/
theorem shared_all_low_ordered_impossible
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hcountA : classCount w .A = 2)
    (hcountH : classCount w .H = 1)
    (hcountL : classCount w .L = 3)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L →
      (29 / 20 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2) : False := by
  let cost (i : Fin 6) : ℝ :=
    ((sharedAllLowCost (w i) (w (i + 1)) : ℕ) : ℝ) *
      Real.pi / 1800
  have hcost (i : Fin 6) : cost i ≤ sixGap φ i :=
    (shared_all_low_gap_cost q hsep φ hmono harg hfirst hlast
      w hA hH hL i).1
  have hAexists : ∃ i : Fin 6, w i = .A := by
    by_contra hnone
    have hzero : classCount w .A = 0 := by
      unfold classCount
      have hempty : (Finset.univ.filter (fun i : Fin 6 =>
          w i = .A)) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          exact False.elim (hnone ⟨i, hi⟩)
        · intro hi
          simp at hi
      simp [hempty]
    omega
  obtain ⟨i, hi⟩ := hAexists
  have hstrict : cost i < sixGap φ i :=
    (shared_all_low_gap_cost q hsep φ hmono harg hfirst hlast
      w hA hH hL i).2 hi
  have hsumlt : (∑ j : Fin 6, cost j) <
      ∑ j : Fin 6, sixGap φ j :=
    Finset.sum_lt_sum (fun j _ => hcost j)
      ⟨i, Finset.mem_univ i, hstrict⟩
  have hq := shared_all_other_touching_low_cost_ge_full_turn
    w hcountA hcountH hcountL
  have hsumcost : 2 * Real.pi ≤ ∑ j : Fin 6, cost j := by
    have hcast : (3600 : ℝ) ≤
        ((sharedAllLowBudget w : ℕ) : ℝ) := by exact_mod_cast hq
    unfold sharedAllLowBudget at hcast
    dsimp [cost]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    push_cast at hcast
    nlinarith [mul_nonneg (sub_nonneg.mpr hcast) Real.pi_pos.le]
  rw [sixGap_sum] at hsumlt
  linarith

/-- The six actual center directions are distinct throughout the
all-low radius rectangle, so polar-angle sorting is a permutation. -/
private theorem six_polarArg_injective
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (hlo : ∀ i, (699 / 1000 : ℝ) ≤ ‖q i‖)
    (hhi : ∀ i, ‖q i‖ ≤ 2385436 / 1000000) :
    Function.Injective (fun i => polarArg (q i)) := by
  intro i j harg
  by_contra hij
  have hd := hsep i j hij
  have hd2 : 4 ≤ dist (q i) (q j) ^ 2 := by
    nlinarith [dist_nonneg (x := q i) (y := q j)]
  rw [dist_eq_norm, norm_sub_sq_real] at hd2
  have hdot := polar_inner (q i) (q j)
  change polarArg (q i) = polarArg (q j) at harg
  rw [harg, sub_self, Real.cos_zero] at hdot
  have hloi := hlo i
  have hloj := hlo j
  have hhii := hhi i
  have hhij := hhi j
  nlinarith

def sharedAllLowRawKind (i : Fin 6) : M2Kind :=
  if i.val < 2 then .A else if i.val = 2 then .H else .L

/-- Label-free form of the all-low obstruction. Labels `0,1` are the
two non-outer centers, `2` is their shared blocker, and `3,4,5` are
the other touching inner centers. -/
theorem shared_all_low_six_centers_impossible
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (hrad : ∀ i, if i.val < 2 then
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧
        ‖q i‖ ≤ 1301 / 1000
      else if i.val = 2 then
        (2 : ℝ) ≤ ‖q i‖ ∧
          ‖q i‖ ≤ 2385436 / 1000000
      else (29 / 20 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2) : False := by
  classical
  have hlo (i : Fin 6) : (699 / 1000 : ℝ) ≤ ‖q i‖ := by
    have hi := hrad i
    split_ifs at hi <;> linarith [hi.1]
  have hhi (i : Fin 6) : ‖q i‖ ≤ 2385436 / 1000000 := by
    have hi := hrad i
    split_ifs at hi <;> linarith [hi.2]
  have hpolar := six_polarArg_injective q hsep hlo hhi
  let angles : Finset ℝ :=
    Finset.univ.image (fun i : Fin 6 => polarArg (q i))
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
  have hsurj : Function.Surjective src :=
    Finite.surjective_of_injective hsrc
  let sorted : Fin 6 → Plane := fun i => q (src i)
  let w : Fin 6 → M2Kind := fun i => sharedAllLowRawKind (src i)
  have hcount (k : M2Kind) :
      classCount w k = classCount sharedAllLowRawKind k := by
    let S : Finset (Fin 6) := Finset.univ.filter (fun i => w i = k)
    let T : Finset (Fin 6) :=
      Finset.univ.filter (fun i => sharedAllLowRawKind i = k)
    have himage : S.image src = T := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        simpa [S, T, w] using hj
      · intro hi
        obtain ⟨j, rfl⟩ := hsurj i
        apply Finset.mem_image.mpr
        exact ⟨j, by simpa [S, T, w] using hi, rfl⟩
    have hcardimage := Finset.card_image_of_injective S hsrc
    rw [himage] at hcardimage
    simpa [classCount, S, T, w] using hcardimage.symm
  have hcountA : classCount w .A = 2 := by
    rw [hcount]
    decide
  have hcountH : classCount w .H = 1 := by
    rw [hcount]
    decide
  have hcountL : classCount w .L = 3 := by
    rw [hcount]
    decide
  have hfirst : -Real.pi < φ 0 := by
    rw [← harg 0]
    exact (polarArg_range (q (src 0))).1
  have hlast : φ 5 ≤ Real.pi := by
    rw [← harg 5]
    exact (polarArg_range (q (src 5))).2
  have hradSorted (i : Fin 6) :
      match w i with
      | .A => (699 / 1000 : ℝ) ≤ ‖sorted i‖ ∧
          ‖sorted i‖ ≤ 1301 / 1000
      | .H => (2 : ℝ) ≤ ‖sorted i‖ ∧
          ‖sorted i‖ ≤ 2385436 / 1000000
      | .L => (29 / 20 : ℝ) ≤ ‖sorted i‖ ∧ ‖sorted i‖ ≤ 2 := by
    by_cases htwo : (src i).val < 2
    · have hle : (src i).val ≤ 1 := by omega
      simpa [w, sorted, sharedAllLowRawKind, htwo, hle] using
        hrad (src i)
    · by_cases heq : (src i).val = 2
      · have hnle : ¬(src i).val ≤ 1 := by omega
        simpa [w, sorted, sharedAllLowRawKind, htwo, hnle, heq] using
          hrad (src i)
      · have hnle : ¬(src i).val ≤ 1 := by omega
        simpa [w, sorted, sharedAllLowRawKind, htwo, hnle, heq] using
          hrad (src i)
  have hA (i : Fin 6) (hi : w i = .A) :
      (699 / 1000 : ℝ) ≤ ‖sorted i‖ ∧
        ‖sorted i‖ ≤ 1301 / 1000 := by
    simpa [hi] using hradSorted i
  have hH (i : Fin 6) (hi : w i = .H) :
      (2 : ℝ) ≤ ‖sorted i‖ ∧
        ‖sorted i‖ ≤ 2385436 / 1000000 := by
    simpa [hi] using hradSorted i
  have hL (i : Fin 6) (hi : w i = .L) :
      (29 / 20 : ℝ) ≤ ‖sorted i‖ ∧ ‖sorted i‖ ≤ 2 := by
    simpa [hi] using hradSorted i
  have hsepSorted : Separated sorted 2 := by
    intro i j hij
    exact hsep (src i) (src j) (hsrc.ne hij)
  exact shared_all_low_ordered_impossible sorted hsepSorted φ hmono
    harg hfirst hlast w hcountA hcountH hcountL hA hH hL

end CP15
