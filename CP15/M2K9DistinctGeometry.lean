import CP15.M2K9DistinctAngles
import CP15.M2Residual
import CP15.M2K9Geometry
import CP15.M2K9HighCount

set_option maxHeartbeats 0

namespace CP15

open scoped InnerProductSpace

private theorem D_lt_distinct_high_ceiling (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) :
    D b < 2385436 / 1000000 := by
  have hbq : b < (352136 / 100000 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_352136_div_100000
  have hrec : 4 / (352136 / 100000 : ℝ) < 4 / b := by
    apply (div_lt_div_iff₀ (by norm_num) (by linarith)).2
    nlinarith
  unfold D
  linarith

private theorem two_nonOuter_radius_cutoff_gt_17_div_5
    (p : Fin 15 → Plane) (b : ℝ) (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i →
      ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hm2 : 2 ≤ (nonOuterIndices p b).card) :
    17 / 5 < b := by
  have hcut := m2_radius_cutoff p b hb hpack hD hblock hFcap
    hFsmall hm2
  have hs5 : (223 / 100 : ℝ) < Real.sqrt 5 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    have hpos := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  have hs21 : (457 / 100 : ℝ) < Real.sqrt 21 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
    have hpos := Real.sqrt_nonneg (21 : ℝ)
    nlinarith
  linarith

private theorem touching_inner_radius_gt_of_outer
    (p : Fin 15 → Plane) (b : ℝ) (i : Fin 15)
    (ht : TouchesOuter p b i) : b - 2 ≤ ‖p i‖ := by
  obtain ⟨j, _, hj, hc⟩ := ht
  have ht' := norm_add_le (p j - p i) (p i)
  rw [sub_add_cancel] at ht'
  rw [dist_eq_norm] at hc
  have hswap : ‖p j - p i‖ = 2 := by
    simpa only [norm_sub_rev] using hc
  linarith

private theorem distinct_six_polarArg_injective
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

private def distinctRawKind (i : Fin 6) : M2Kind :=
  if i.val < 2 then .A else if i.val < 4 then .H else .L

private def distinctRawIndex
    (target blocker extra : Fin 2 → Fin 15) (i : Fin 6) : Fin 15 :=
  if h : i.val < 2 then target ⟨i.val, h⟩
  else if h₂ : i.val < 4 then blocker ⟨i.val - 2, by omega⟩
  else extra ⟨i.val - 4, by omega⟩

private theorem distinctRawIndex_injective
    (p : Fin 15 → Plane) (b : ℝ)
    (target blocker extra : Fin 2 → Fin 15)
    (htarget : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c))
    (hblocker : ∀ c, TouchesOuter p b (blocker c))
    (hblocker_inj : Function.Injective blocker)
    (hextra : ∀ c, TouchesOuter p b (extra c))
    (hblocker_extra : ∀ c d, blocker c ≠ extra d)
    (hextra_inj : Function.Injective extra) :
    Function.Injective (distinctRawIndex target blocker extra) := by
  intro i j hij
  by_cases hi : i.val < 2
  · by_cases hj : j.val < 2
    · have heq : (⟨i.val, hi⟩ : Fin 2) = ⟨j.val, hj⟩ := by
        apply htarget
        simpa [distinctRawIndex, hi, hj] using hij
      apply Fin.ext
      have hv := congrArg Fin.val heq
      dsimp at hv
      exact hv
    · by_cases hj₂ : j.val < 4
      · have heq : target ⟨i.val, hi⟩ =
            blocker ⟨j.val - 2, by omega⟩ := by
          simpa [distinctRawIndex, hi, hj, hj₂] using hij
        exact False.elim ((hno ⟨i.val, hi⟩).2
          (heq ▸ hblocker ⟨j.val - 2, by omega⟩))
      · have heq : target ⟨i.val, hi⟩ =
            extra ⟨j.val - 4, by omega⟩ := by
          simpa [distinctRawIndex, hi, hj, hj₂] using hij
        exact False.elim ((hno ⟨i.val, hi⟩).2
          (heq ▸ hextra ⟨j.val - 4, by omega⟩))
  · by_cases hi₂ : i.val < 4
    · by_cases hj : j.val < 2
      · have heq : blocker ⟨i.val - 2, by omega⟩ =
            target ⟨j.val, hj⟩ := by
          simpa [distinctRawIndex, hi, hi₂, hj] using hij
        exact False.elim ((hno ⟨j.val, hj⟩).2
          (heq.symm ▸ hblocker ⟨i.val - 2, by omega⟩))
      · by_cases hj₂ : j.val < 4
        · have heq : (⟨i.val - 2, by omega⟩ : Fin 2) =
              ⟨j.val - 2, by omega⟩ := by
            apply hblocker_inj
            simpa [distinctRawIndex, hi, hi₂, hj, hj₂] using hij
          apply Fin.ext
          have hv := congrArg Fin.val heq
          dsimp at hv
          omega
        · have heq : blocker ⟨i.val - 2, by omega⟩ =
              extra ⟨j.val - 4, by omega⟩ := by
            simpa [distinctRawIndex, hi, hi₂, hj, hj₂] using hij
          exact False.elim (hblocker_extra _ _ heq)
    · by_cases hj : j.val < 2
      · have heq : extra ⟨i.val - 4, by omega⟩ =
            target ⟨j.val, hj⟩ := by
          simpa [distinctRawIndex, hi, hi₂, hj] using hij
        exact False.elim ((hno ⟨j.val, hj⟩).2
          (heq.symm ▸ hextra ⟨i.val - 4, by omega⟩))
      · by_cases hj₂ : j.val < 4
        · have heq : extra ⟨i.val - 4, by omega⟩ =
              blocker ⟨j.val - 2, by omega⟩ := by
            simpa [distinctRawIndex, hi, hi₂, hj, hj₂] using hij
          exact False.elim (hblocker_extra _ _ heq.symm)
        · have heq : (⟨i.val - 4, by omega⟩ : Fin 2) =
              ⟨j.val - 4, by omega⟩ := by
            apply hextra_inj
            simpa [distinctRawIndex, hi, hi₂, hj, hj₂] using hij
          apply Fin.ext
          have hv := congrArg Fin.val heq
          dsimp at hv
          omega
noncomputable def distinctForwardArc (φ : Fin 6 → ℝ)
    (a b : Fin 6) : ℝ :=
  if a.val < b.val then φ b - φ a else φ b + 2 * Real.pi - φ a

private theorem distinct_span_two
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (θ : ℝ)
    (hlin : ∀ k : Fin 6, k.val < 5 → θ ≤ φ (k + 1) - φ k)
    (i j : Fin 6) (hspan : i.val + 2 ≤ j.val) :
    2 * θ ≤ φ j - φ i := by
  let i₁ : Fin 6 := ⟨i.val + 1, by omega⟩
  let i₂ : Fin 6 := ⟨i.val + 2, by omega⟩
  have hi₁eq : i + 1 = i₁ := by
    apply Fin.ext
    change (i.val + 1) % 6 = i.val + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hi₂eq : i₁ + 1 = i₂ := by
    apply Fin.ext
    change (i.val + 2) % 6 = i.val + 2
    exact Nat.mod_eq_of_lt (by omega)
  have hg₁ : θ ≤ φ i₁ - φ i := by
    have hg := hlin i (by omega)
    rw [hi₁eq] at hg
    exact hg
  have hg₂ : θ ≤ φ i₂ - φ i₁ := by
    have hk₁ : i₁.val < 5 := by dsimp [i₁]; omega
    have hg := hlin i₁ hk₁
    rw [hi₂eq] at hg
    exact hg
  have hi₂le : i₂ ≤ j := by
    exact Fin.mk_le_mk.mpr (by omega)
  have hφle : φ i₂ ≤ φ j := by
    by_cases heq : i₂ = j
    · simpa [heq]
    · exact (hmono (lt_of_le_of_ne hi₂le heq)).le
  have hsum : 2 * θ ≤ (φ i₁ - φ i) + (φ i₂ - φ i₁) := by
    nlinarith [hg₁, hg₂]
  have hcollapse : (φ i₁ - φ i) + (φ i₂ - φ i₁) = φ i₂ - φ i := by ring
  rw [hcollapse] at hsum
  linarith

private theorem distinct_wrap_two
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hlin : ∀ k : Fin 6, k.val < 5 → θ ≤ φ (k + 1) - φ k)
    (hwrap : θ ≤ φ 0 + 2 * Real.pi - φ 5)
    (lo hi : Fin 6) (hlohi : lo.val < hi.val)
    (hneigh : ¬cyclicNeighbor hi lo) :
    2 * θ ≤ distinctForwardArc φ hi lo := by
  have harc : distinctForwardArc φ hi lo =
      φ lo + 2 * Real.pi - φ hi := by
    simp [distinctForwardArc, not_lt_of_gt hlohi]
  rw [harc]
  by_cases hhi3 : hi.val < 4
  · have hspan := distinct_span_two φ hmono θ hlin hi 5 (by omega)
    have hphi0lo : φ 0 ≤ φ lo := by
      by_cases hz : lo.val = 0
      · have hz' : lo = 0 := Fin.ext hz
        rw [hz']
      · exact (hmono (by omega)).le
    have hdecomp : φ lo + 2 * Real.pi - φ hi =
        (φ 5 - φ hi) + (φ 0 + 2 * Real.pi - φ 5) +
          (φ lo - φ 0) := by ring
    rw [hdecomp]
    have hw0 : 0 ≤ φ 0 + 2 * Real.pi - φ 5 := by linarith
    have hlo0 : 0 ≤ φ lo - φ 0 := by linarith
    linarith
  · have hhi4or5 : hi.val = 4 ∨ hi.val = 5 := by omega
    rcases hhi4or5 with hhi4 | hhi5
    · have hg4 : θ ≤ φ 5 - φ 4 := by
        simpa using hlin 4 (by norm_num)
      have hphi0lo : φ 0 ≤ φ lo := by
        by_cases hz : lo.val = 0
        · have hz' : lo = 0 := Fin.ext hz
          rw [hz']
        · exact (hmono (by omega)).le
      have hdecomp : φ lo + 2 * Real.pi - φ hi =
          (φ 5 - φ 4) + (φ 0 + 2 * Real.pi - φ 5) +
            (φ lo - φ 0) := by
        have hhi' : hi = 4 := Fin.ext hhi4
        rw [hhi']
        ring
      rw [hdecomp]
      have hlo0 : 0 ≤ φ lo - φ 0 := by linarith
      linarith [hwrap, hg4]
    · have hlo_ne_zero : lo.val ≠ 0 := by
        intro hzero
        have hwrapNeighbor : cyclicNeighbor hi lo := by
          left
          apply Fin.ext
          change lo.val = (hi.val + 1) % 6
          rw [hzero, hhi5]
        exact hneigh hwrapNeighbor
      have hphi1lo : φ 1 ≤ φ lo := by
        by_cases hEq : lo.val = 1
        · have hEq' : lo = 1 := Fin.ext hEq
          rw [hEq']
        · exact (hmono (by omega)).le
      have hg0 : θ ≤ φ 1 - φ 0 := by
        simpa using hlin 0 (by norm_num)
      have hdecomp : φ lo + 2 * Real.pi - φ hi =
          (φ 0 + 2 * Real.pi - φ 5) + (φ lo - φ 0) := by
        have hhi' : hi = 5 := Fin.ext hhi5
        rw [hhi']
        ring
      rw [hdecomp]
      have hlo1 : φ 1 - φ 0 ≤ φ lo - φ 0 := sub_le_sub_right hphi1lo _
      linarith [hwrap, hg0, hlo1]

private theorem distinct_arcs_ge_two_gaps
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hlin : ∀ k : Fin 6, k.val < 5 → θ ≤ φ (k + 1) - φ k)
    (hwrap : θ ≤ φ 0 + 2 * Real.pi - φ 5)
    (a b : Fin 6) (hab : a ≠ b)
    (hneigh : ¬cyclicNeighbor a b) :
    2 * θ ≤ distinctForwardArc φ a b ∧
      2 * θ ≤ distinctForwardArc φ b a := by
  by_cases hlt : a.val < b.val
  · have hspan : a.val + 2 ≤ b.val := by
      by_contra h
      have hstep : b.val = a.val + 1 := by omega
      have hsucc : b = a + 1 := by
        apply Fin.ext
        change b.val = (a.val + 1) % 6
        rw [Nat.mod_eq_of_lt (by omega)]
        exact hstep
      exact hneigh (Or.inl hsucc)
    have hforward := distinct_span_two φ hmono θ hlin a b hspan
    have hneigh' : ¬cyclicNeighbor b a := by
      intro hn
      apply hneigh
      rcases hn with hn | hn
      · exact Or.inr hn
      · exact Or.inl hn
    have hbackward := distinct_wrap_two φ hmono θ hθ hlin hwrap a b
      (by omega) hneigh'
    constructor
    · simpa [distinctForwardArc, hlt] using hforward
    · simpa [distinctForwardArc, not_lt_of_gt hlt] using hbackward
  · have hgt : b.val < a.val := by
      have hneqval : a.val ≠ b.val := by
        intro heq
        apply hab
        apply Fin.ext
        exact heq
      omega
    have hspan : b.val + 2 ≤ a.val := by
      by_contra h
      have hstep : a.val = b.val + 1 := by omega
      have hsucc : a = b + 1 := by
        apply Fin.ext
        change a.val = (b.val + 1) % 6
        rw [Nat.mod_eq_of_lt (by omega)]
        exact hstep
      exact hneigh (Or.inr hsucc)
    have hforward := distinct_wrap_two φ hmono θ hθ hlin hwrap b a
      (by omega) hneigh
    have hbackward := distinct_span_two φ hmono θ hlin b a hspan
    constructor
    · simpa [distinctForwardArc, not_lt_of_gt hgt] using hforward
    · simpa [distinctForwardArc, hgt] using hbackward

private theorem cos_positive_arc_short
    (d : ℝ) (hd0 : 0 ≤ d) (hd2 : d ≤ 2 * Real.pi)
    (hcos : 0 < Real.cos d) :
    d < Real.pi / 2 ∨ 2 * Real.pi - d < Real.pi / 2 := by
  by_cases hsmall : d < Real.pi / 2
  · exact Or.inl hsmall
  · have hlarge : 3 * Real.pi / 2 < d := by
      by_contra hnot
      have hnot' : ¬ (Real.pi + Real.pi / 2) < d := by
        intro hgt
        apply hnot
        nlinarith
      have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le
        (le_of_not_gt hsmall) (le_of_not_gt hnot')
      linarith
    exact Or.inr (by linarith)

private theorem distinct_short_contact_forces_neighbor
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (hrange : ∀ i, -Real.pi < φ i ∧ φ i ≤ Real.pi)
    (θ : ℝ) (hθ : Real.pi / 2 < 2 * θ)
    (hlin : ∀ k : Fin 6, k.val < 5 → θ ≤ φ (k + 1) - φ k)
    (hwrap : θ ≤ φ 0 + 2 * Real.pi - φ 5)
    (a b : Fin 6) (hab : a ≠ b)
    (hcos : 0 < Real.cos (φ a - φ b)) :
    cyclicNeighbor a b := by
  by_contra hneigh
  have hθpos : 0 ≤ θ := by
    have hπ : 0 < Real.pi := Real.pi_pos
    linarith
  have harcs := distinct_arcs_ge_two_gaps φ hmono θ hθpos hlin hwrap
    a b hab hneigh
  have hd0 : 0 ≤ distinctForwardArc φ a b := by
    by_cases hlt : a.val < b.val
    · simp [distinctForwardArc, hlt]
      exact (hmono (by omega)).le
    · have hgt : b.val < a.val := by
        have hneqval : a.val ≠ b.val := by
          intro heq
          exact hab (Fin.ext heq)
        omega
      simp [distinctForwardArc, not_lt_of_gt hgt]
      have hpos : φ b < φ a := hmono (by omega)
      have hb := (hrange b).1
      have ha := (hrange a).2
      linarith
  have hd2 : distinctForwardArc φ a b ≤ 2 * Real.pi := by
    by_cases hlt : a.val < b.val
    · simp [distinctForwardArc, hlt]
      have hb := (hrange b).2
      have ha := (hrange a).1
      linarith
    · have hgt : b.val < a.val := by
        have hneqval : a.val ≠ b.val := by
          intro heq
          exact hab (Fin.ext heq)
        omega
      simp [distinctForwardArc, not_lt_of_gt hgt]
      have hpos : φ b < φ a := hmono (by omega)
      linarith
  have hcosArc : 0 < Real.cos (distinctForwardArc φ a b) := by
    by_cases hlt : a.val < b.val
    · have hcos' : 0 < Real.cos (φ b - φ a) := by
        have heq : φ b - φ a = -(φ a - φ b) := by ring
        rw [heq, Real.cos_neg]
        exact hcos
      simpa [distinctForwardArc, hlt] using hcos'
    · have hgt : b.val < a.val := by
        have hneqval : a.val ≠ b.val := by
          intro heq
          exact hab (Fin.ext heq)
        omega
      have hcosrev : 0 < Real.cos (φ b - φ a) := by
        have heq : φ b - φ a = -(φ a - φ b) := by ring
        rw [heq, Real.cos_neg]
        exact hcos
      have heq : distinctForwardArc φ a b =
          (φ b - φ a) + 2 * Real.pi := by
        simp [distinctForwardArc, not_lt_of_gt hgt]
        ring
      rw [heq, Real.cos_add_two_pi]
      exact hcosrev
  have hshort := cos_positive_arc_short
    (distinctForwardArc φ a b) hd0 hd2 hcosArc
  rcases hshort with hshort | hshort
  · linarith [harcs.1]
  · have hpi : Real.pi / 2 < 2 * θ := by
      exact hθ
    have hcomp : distinctForwardArc φ b a =
        2 * Real.pi - distinctForwardArc φ a b := by
      by_cases hlt : a.val < b.val
      · simp [distinctForwardArc, hlt, not_lt_of_gt hlt]
        ring
      · have hgt : b.val < a.val := by
          have hneqval : a.val ≠ b.val := by
            intro heq
            exact hab (Fin.ext heq)
          omega
        simp [distinctForwardArc, hgt, not_lt_of_gt hgt]
        ring
    rw [hcomp] at harcs
    linarith
/-- Rebuild the six-center class model directly from two distinct selected
strict blockers.  The two residual touching centers come from the exact
four-element touching-inner set; their upper radius bound follows from the
independent high-center count.  All radii and the finite class budget are
therefore consequences of the actual packing data. -/
theorem distinct_k9_actual_six_order_budget
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i →
      ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hK9 : (boundarySet p b).card = 9)
    (hm2 : (nonOuterIndices p b).card = 2)
    (target blocker outer : Fin 2 → Fin 15)
    (htarget : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c))
    (hdata : ∀ c, blocker c ≠ target c ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
      outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
      dist (p (blocker c)) (p (outer c)) = 2 ∧
      ‖p (target c)‖ ^ 2 <
        ⟪p (blocker c), p (target c)⟫_ℝ)
    (hblocker_ne : blocker 0 ≠ blocker 1) :
    ∃ q : Fin 6 → Plane, ∃ φ : Fin 6 → ℝ,
      ∃ w : Fin 6 → M2Kind,
        Separated q 2 ∧ StrictMono φ ∧
        (∀ i, polarArg (q i) = φ i) ∧
        -Real.pi < φ 0 ∧ φ 5 ≤ Real.pi ∧
        classCount w .A = 2 ∧ classCount w .H = 2 ∧
        classCount w .L = 2 ∧
        (∀ i, w i = .A →
          (699 / 1000 : ℝ) ≤ ‖q i‖ ∧
            ‖q i‖ ≤ 1301 / 1000) ∧
        (∀ i, w i = .H →
          (2 : ℝ) ≤ ‖q i‖ ∧
            ‖q i‖ ≤ 2385436 / 1000000) ∧
        (∀ i, w i = .L →
          (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2) ∧
        (∃ apos hpos : Fin 2 → Fin 6,
          (∀ c, w (apos c) = .A) ∧
          (∀ c, w (hpos c) = .H) ∧
          (∀ c, q (apos c) = p (target c)) ∧
          (∀ c, q (hpos c) = p (blocker c)) ∧
          Function.Injective apos ∧ Function.Injective hpos ∧
          (∀ c, cyclicNeighbor (apos c) (hpos c))) ∧
        matchedAdjacentHighs w ∧
        classBudget w ≤ 3600 ∧
        (∃ ix : Fin 6 → Fin 15,
          Function.Injective ix ∧ (∀ i, q i = p (ix i)) ∧
          (∀ i, ‖p (ix i)‖ < b) ∧
          (∀ j, ‖p j‖ < b → ∃ i, ix i = j)) := by
  classical
  have hm2le : 2 ≤ (nonOuterIndices p b).card := by rw [hm2]
  have hbcut : 17 / 5 < b :=
    two_nonOuter_radius_cutoff_gt_17_div_5 p b hb hpack hD
      hFcap hFsmall hblock hm2le
  have hb3 : 3 < b := by linarith
  have hFhi : F b < 1301 / 1000 :=
    F_lt_1301_div_1000_of_le_candidateB b hb hbB
  have htarget_hi (c : Fin 2) :
      ‖p (target c)‖ ≤ 1301 / 1000 :=
    (hFcap (target c) (hno c).1 (hno c).2).trans hFhi.le
  have htarget_sep : 2 ≤ dist (p (target 0)) (p (target 1)) :=
    hpack.2 _ _ (htarget.ne (by decide))
  have htri : dist (p (target 0)) (p (target 1)) ≤
      ‖p (target 0)‖ + ‖p (target 1)‖ := by
    simpa [dist_eq_norm] using norm_sub_le (p (target 0)) (p (target 1))
  have hsum : (2 : ℝ) ≤ ‖p (target 0)‖ + ‖p (target 1)‖ :=
    htarget_sep.trans htri
  have htarget_lo0 : (699 / 1000 : ℝ) ≤ ‖p (target 0)‖ := by
    linarith [hsum, htarget_hi (1 : Fin 2)]
  have htarget_lo1 : (699 / 1000 : ℝ) ≤ ‖p (target 1)‖ := by
    linarith [hsum, htarget_hi (0 : Fin 2)]
  have htarget_lo (c : Fin 2) :
      (699 / 1000 : ℝ) ≤ ‖p (target c)‖ := by
    fin_cases c
    · exact htarget_lo0
    · exact htarget_lo1
  have hDhi := D_lt_distinct_high_ceiling b hb hbB
  have hblocker_hi (c : Fin 2) :
      ‖p (blocker c)‖ ≤ 2385436 / 1000000 :=
    (hD (blocker c) (hdata c).2.2.1).trans hDhi |>.le
  have htouch (c : Fin 2) : TouchesOuter p b (blocker c) :=
    ⟨outer c, (hdata c).2.2.2.2.1,
      (hdata c).2.2.2.2.2.1, (hdata c).2.2.2.2.2.2.1⟩
  let T := touchingInnerSet p b
  have hTcard : T.card = 4 :=
    k9_m2_touching_inner_card_four p b hpack.1 hK9 hm2
  have hblocker_mem (c : Fin 2) : blocker c ∈ T := by
    simpa [T, touchingInnerSet] using
      (⟨(hdata c).2.2.1, htouch c⟩ :
        ‖p (blocker c)‖ < b ∧ TouchesOuter p b (blocker c))
  let S : Finset (Fin 15) := {blocker 0, blocker 1}
  have hScard : S.card = 2 := by
    simp [S, hblocker_ne]
  have hSsub : S ⊆ T := by
    intro i hi
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · simpa [hi] using hblocker_mem 0
    · simpa [hi] using hblocker_mem 1
  let R := T \ S
  have hRcard : R.card = 2 := by
    rw [Finset.card_sdiff_of_subset hSsub, hTcard, hScard]
  have hRlarge : Fintype.card (Fin 2) ≤ R.card := by
    simp [hRcard]
  obtain ⟨extra, hextraR⟩ :=
    Function.Embedding.exists_of_card_le_finset hRlarge
  have hextra_mem (c : Fin 2) : extra c ∈ T ∧ extra c ∉ S := by
    have hc := hextraR ⟨c, rfl⟩
    exact (Finset.mem_sdiff.mp hc)
  have hextra_touch (c : Fin 2) : TouchesOuter p b (extra c) := by
    have ht : extra c ∈ touchingInnerSet p b := by
      simpa [T] using (hextra_mem c).1
    have ht' : ‖p (extra c)‖ < b ∧ TouchesOuter p b (extra c) := by
      simpa [touchingInnerSet] using ht
    exact ht'.2
  have hextra_inj : Function.Injective extra := extra.injective
  have hblocker_inj : Function.Injective blocker := by
    intro c d h
    fin_cases c <;> fin_cases d <;> simp_all
  have hblocker_extra (c d : Fin 2) : blocker c ≠ extra d := by
    intro heq
    have hinS : extra d ∈ S := by
      rw [← heq]
      fin_cases c <;> simp [S]
    exact (hextra_mem d).2 hinS
  have hidxinj := distinctRawIndex_injective p b target blocker extra
    htarget hno htouch hblocker_inj hextra_touch hblocker_extra
    hextra_inj
  let idx := distinctRawIndex target blocker extra
  let q : Fin 6 → Plane := fun i => p (idx i)
  have hsepq : Separated q 2 := by
    intro i j hij
    exact hpack.2 (idx i) (idx j) (hidxinj.ne hij)
  let rawRad (i : Fin 6) : Prop :=
    if i.val < 2 then
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000
    else if i.val < 4 then
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000
    else (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2
  have hhighCount : ((T.filter (fun i => 2 < ‖p i‖)).card) ≤ 2 := by
    simpa [T] using
      (k9_high_touching_inner_count_le_two p b hb3 hbB hpack.2
        hD hK9)
  have hextra_hi (c : Fin 2) : ‖p (extra c)‖ ≤ 2 := by
    by_contra hnot
    have hgt : 2 < ‖p (extra c)‖ := lt_of_not_ge hnot
    let H := T.filter (fun i => 2 < ‖p i‖)
    let U : Finset (Fin 15) := {blocker 0, blocker 1, extra c}
    have hUsub : U ⊆ H := by
      intro i hi
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [H, Finset.mem_filter]
      rcases hi with rfl | rfl | rfl
      · exact ⟨hblocker_mem 0, (hdata 0).2.2.2.1⟩
      · exact ⟨hblocker_mem 1, (hdata 1).2.2.2.1⟩
      · exact ⟨(hextra_mem c).1, hgt⟩
    have hne0 : blocker 0 ≠ extra c := hblocker_extra 0 c
    have hne1 : blocker 1 ≠ extra c := hblocker_extra 1 c
    have hUcard : U.card = 3 := by
      simp [U, hblocker_ne, hne0, hne1]
    have hle := Finset.card_le_card hUsub
    have hle' : 3 ≤ H.card := by simpa [hUcard] using hle
    have hHcount : H.card ≤ 2 := by simpa [H] using hhighCount
    have hHfalse : False := by omega
    exact hHfalse
  have hextra_lo (c : Fin 2) : (7 / 5 : ℝ) ≤ ‖p (extra c)‖ := by
    have hbase := touching_inner_radius_gt_of_outer p b (extra c)
      (hextra_touch c)
    linarith [hbcut]
  have hrawRad (i : Fin 6) : rawRad i := by
    by_cases hi : i.val < 2
    · have hi' : i.val ≤ 1 := by omega
      have hr : (699 / 1000 : ℝ) ≤ ‖p (target ⟨i.val, hi⟩)‖ ∧
          ‖p (target ⟨i.val, hi⟩)‖ ≤ 1301 / 1000 :=
        ⟨htarget_lo ⟨i.val, hi⟩, htarget_hi ⟨i.val, hi⟩⟩
      simpa [rawRad, q, idx, distinctRawIndex, hi, hi'] using hr
    · by_cases hi₂ : i.val < 4
      · have hi₂' : i.val ≤ 3 := by omega
        have hi' : ¬i.val ≤ 1 := by omega
        have hr : (2 : ℝ) ≤ ‖p (blocker ⟨i.val - 2, by omega⟩)‖ ∧
            ‖p (blocker ⟨i.val - 2, by omega⟩)‖ ≤ 2385436 / 1000000 :=
          ⟨(hdata ⟨i.val - 2, by omega⟩).2.2.2.1.le,
            hblocker_hi ⟨i.val - 2, by omega⟩⟩
        simpa [rawRad, q, idx, distinctRawIndex, hi, hi', hi₂, hi₂'] using hr
      · have hi₂' : ¬i.val ≤ 3 := by omega
        have hi' : ¬i.val ≤ 1 := by omega
        have hr : (7 / 5 : ℝ) ≤ ‖p (extra ⟨i.val - 4, by omega⟩)‖ ∧
            ‖p (extra ⟨i.val - 4, by omega⟩)‖ ≤ 2 :=
          ⟨hextra_lo ⟨i.val - 4, by omega⟩,
            hextra_hi ⟨i.val - 4, by omega⟩⟩
        simpa [rawRad, q, idx, distinctRawIndex, hi, hi', hi₂, hi₂'] using hr
  have hlo (i : Fin 6) : (699 / 1000 : ℝ) ≤ ‖q i‖ := by
    have hr := hrawRad i
    dsimp [rawRad] at hr
    split_ifs at hr <;> linarith
  have hhi (i : Fin 6) : ‖q i‖ ≤ 2385436 / 1000000 := by
    have hr := hrawRad i
    dsimp [rawRad] at hr
    split_ifs at hr <;> linarith
  have hpolar := distinct_six_polarArg_injective q hsepq hlo hhi
  let angles : Finset ℝ := Finset.univ.image (fun i : Fin 6 => polarArg (q i))
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
    intro i j heq
    apply hmono.injective
    calc
      φ i = polarArg (q (src i)) := (harg i).symm
      _ = polarArg (q (src j)) := by rw [heq]
      _ = φ j := harg j
  have hsurj : Function.Surjective src :=
    Finite.surjective_of_injective hsrc
  let sorted : Fin 6 → Plane := fun i => q (src i)
  let w : Fin 6 → M2Kind := fun i => distinctRawKind (src i)
  have hcount (k : M2Kind) :
      classCount w k = classCount distinctRawKind k := by
    let A : Finset (Fin 6) := Finset.univ.filter (fun i => w i = k)
    let B : Finset (Fin 6) :=
      Finset.univ.filter (fun i => distinctRawKind i = k)
    have himage : A.image src = B := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        simpa [A, B, w] using hj
      · intro hi
        obtain ⟨j, rfl⟩ := hsurj i
        apply Finset.mem_image.mpr
        exact ⟨j, by simpa [A, B, w] using hi, rfl⟩
    have hc := Finset.card_image_of_injective A hsrc
    rw [himage] at hc
    simpa [classCount, A, B] using hc.symm
  have hcountA : classCount w .A = 2 := by
    rw [hcount]
    decide
  have hcountH : classCount w .H = 2 := by
    rw [hcount]
    decide
  have hcountL : classCount w .L = 2 := by
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
      | .L => (7 / 5 : ℝ) ≤ ‖sorted i‖ ∧ ‖sorted i‖ ≤ 2 := by
    have hr := hrawRad (src i)
    dsimp [rawRad, w, sorted, q, idx] at hr ⊢
    by_cases hi : (src i).val < 2
    · simp [distinctRawKind, hi] at hr ⊢
      exact hr
    · by_cases hi₂ : (src i).val < 4
      · simp [distinctRawKind, hi, hi₂] at hr ⊢
        exact hr
      · simp [distinctRawKind, hi, hi₂] at hr ⊢
        exact hr
  have hA (i : Fin 6) (hi : w i = .A) :
      (699 / 1000 : ℝ) ≤ ‖sorted i‖ ∧
        ‖sorted i‖ ≤ 1301 / 1000 := by
    simpa [hi] using hradSorted i
  have hH (i : Fin 6) (hi : w i = .H) :
      (2 : ℝ) ≤ ‖sorted i‖ ∧
        ‖sorted i‖ ≤ 2385436 / 1000000 := by
    simpa [hi] using hradSorted i
  have hL (i : Fin 6) (hi : w i = .L) :
      (7 / 5 : ℝ) ≤ ‖sorted i‖ ∧ ‖sorted i‖ ≤ 2 := by
    simpa [hi] using hradSorted i
  have hsepSorted : Separated sorted 2 := by
    intro i j hij
    exact hsepq (src i) (src j) (hsrc.ne hij)
  let pos (r : Fin 6) : Fin 6 := Classical.choose (hsurj r)
  have hpos_src (r : Fin 6) : src (pos r) = r :=
    Classical.choose_spec (hsurj r)
  let rawA (c : Fin 2) : Fin 6 := ⟨c.val, by omega⟩
  let rawH (c : Fin 2) : Fin 6 := ⟨c.val + 2, by omega⟩
  let apos (c : Fin 2) : Fin 6 := pos (rawA c)
  let hpos (c : Fin 2) : Fin 6 := pos (rawH c)
  have hAlabel (c : Fin 2) : w (apos c) = .A := by
    change distinctRawKind (src (pos (rawA c))) = .A
    rw [hpos_src]
    have hc : c.val < 2 := c.isLt
    have hr : (rawA c).val < 2 := by dsimp [rawA]; omega
    simp [distinctRawKind, rawA, hr]
  have hHlabel (c : Fin 2) : w (hpos c) = .H := by
    change distinctRawKind (src (pos (rawH c))) = .H
    rw [hpos_src]
    have hc : c.val < 2 := c.isLt
    have hnot : ¬ (rawH c).val < 2 := by dsimp [rawH]; omega
    have hlt : (rawH c).val < 4 := by dsimp [rawH]; omega
    simp [distinctRawKind, rawH, hnot, hlt]
  have hrawAH_ne (c : Fin 2) : rawA c ≠ rawH c := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [rawA, rawH] at hv
    omega
  have hposAH_ne (c : Fin 2) : apos c ≠ hpos c := by
    intro heq
    apply hrawAH_ne c
    calc
      rawA c = src (apos c) := (hpos_src (rawA c)).symm
      _ = src (hpos c) := by rw [heq]
      _ = rawH c := hpos_src (rawH c)
  have hApos_ne : apos 0 ≠ apos 1 := by
    intro heq
    have hr : rawA (0 : Fin 2) = rawA 1 := by
      calc
        rawA 0 = src (apos 0) := (hpos_src (rawA 0)).symm
        _ = src (apos 1) := by rw [heq]
        _ = rawA 1 := hpos_src (rawA 1)
    have hv := congrArg Fin.val hr
    dsimp [rawA] at hv
    norm_num at hv
  have hHpos_ne : hpos 0 ≠ hpos 1 := by
    intro heq
    have hr : rawH (0 : Fin 2) = rawH 1 := by
      calc
        rawH 0 = src (hpos 0) := (hpos_src (rawH 0)).symm
        _ = src (hpos 1) := by rw [heq]
        _ = rawH 1 := hpos_src (rawH 1)
    have hv := congrArg Fin.val hr
    dsimp [rawH] at hv
    norm_num at hv
  have hqA (c : Fin 2) : sorted (apos c) = p (target c) := by
    change q (src (apos c)) = p (target c)
    rw [hpos_src]
    have hc : c.val < 2 := c.isLt
    have hr : (rawA c).val < 2 := by dsimp [rawA]; omega
    have hc' : c.val ≤ 1 := by omega
    simp [q, idx, distinctRawIndex, rawA, hc']
  have hqH (c : Fin 2) : sorted (hpos c) = p (blocker c) := by
    change q (src (hpos c)) = p (blocker c)
    rw [hpos_src]
    have hc : c.val < 2 := c.isLt
    have hnot : ¬ (rawH c).val < 2 := by dsimp [rawH]; omega
    have hlt : (rawH c).val < 4 := by dsimp [rawH]; omega
    have hnot' : ¬ (c.val + 2 ≤ 1) := by omega
    have hlt' : c.val + 2 < 4 := by omega
    simp [q, idx, distinctRawIndex, rawH, hnot', hlt', Nat.add_sub_cancel]
  have θpos : (0 : ℝ) ≤ 49 * Real.pi / 180 := by positivity
  have hlin : ∀ k : Fin 6, k.val < 5 →
      49 * Real.pi / 180 ≤ φ (k + 1) - φ k := by
    intro k hk
    have hk5 : k ≠ 5 := by
      intro heq
      have hv := congrArg Fin.val heq
      omega
    have hg := distinct_order_gap_at_least_49 sorted hsepSorted φ
      hmono harg hfirst hlast w hA hH hL k
    simpa [distinctSixGap, hk5] using hg
  have hwrap : 49 * Real.pi / 180 ≤ φ 0 + 2 * Real.pi - φ 5 := by
    simpa [distinctSixGap] using
      (distinct_order_gap_at_least_49 sorted hsepSorted φ hmono harg
        hfirst hlast w hA hH hL (5 : Fin 6))
  have htheta : Real.pi / 2 < 2 * (49 * Real.pi / 180) := by
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith
  have hphi_range (i : Fin 6) : -Real.pi < φ i ∧ φ i ≤ Real.pi := by
    constructor
    · rw [← harg i]
      exact (polarArg_range (q (src i))).1
    · rw [← harg i]
      exact (polarArg_range (q (src i))).2
  have hadj (c : Fin 2) : cyclicNeighbor (apos c) (hpos c) := by
    have hdot : ‖sorted (apos c)‖ ^ 2 <
        ⟪sorted (hpos c), sorted (apos c)⟫_ℝ := by
      simpa [hqA, hqH] using (hdata c).2.2.2.2.2.2.2
    have hpolar := polar_inner (sorted (hpos c)) (sorted (apos c))
    rw [harg (hpos c), harg (apos c)] at hpolar
    have hposA : 0 < ‖sorted (apos c)‖ := by
      exact lt_of_lt_of_le (by norm_num) (hA (apos c) (hAlabel c)).1
    have hposH : 0 < ‖sorted (hpos c)‖ := by
      exact lt_of_lt_of_le (by norm_num) (hH (hpos c) (hHlabel c)).1
    have hprod : 0 < ‖sorted (hpos c)‖ * ‖sorted (apos c)‖ :=
      mul_pos hposH hposA
    have hcosHT : 0 < Real.cos (φ (hpos c) - φ (apos c)) := by
      by_contra hn
      have hcosle : Real.cos (φ (hpos c) - φ (apos c)) ≤ 0 := le_of_not_gt hn
      have hnonpos : ‖sorted (hpos c)‖ * ‖sorted (apos c)‖ *
          Real.cos (φ (hpos c) - φ (apos c)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hprod.le hcosle
      rw [hpolar] at hdot
      have hsquare : 0 ≤ ‖sorted (apos c)‖ ^ 2 := sq_nonneg _
      linarith
    have hcosAH : 0 < Real.cos (φ (apos c) - φ (hpos c)) := by
      rw [show φ (apos c) - φ (hpos c) =
        -(φ (hpos c) - φ (apos c)) by ring, Real.cos_neg]
      exact hcosHT
    exact distinct_short_contact_forces_neighbor φ hmono
      hphi_range (49 * Real.pi / 180)
      htheta hlin hwrap (apos c) (hpos c)
      (hposAH_ne c) hcosAH
  have hmatch : matchedAdjacentHighs w := by
    refine ⟨apos 0, apos 1, hpos 0, hpos 1, hApos_ne, hHpos_ne,
      hAlabel 0, hAlabel 1, hHlabel 0, hHlabel 1, ?_, ?_⟩
    · exact hadj 0
    · exact hadj 1
  have hbudget := distinct_order_class_budget sorted hsepSorted
    φ hmono harg hfirst hlast w hA hH hL
  have hextra_inner (c : Fin 2) : ‖p (extra c)‖ < b := by
    have ht : ‖p (extra c)‖ < b ∧ TouchesOuter p b (extra c) := by
      simpa [T, touchingInnerSet] using (hextra_mem c).1
    exact ht.1
  have hidx_inner (i : Fin 6) : ‖p (idx i)‖ < b := by
    fin_cases i
    · simpa [idx, distinctRawIndex] using (hno 0).1
    · simpa [idx, distinctRawIndex] using (hno 1).1
    · simpa [idx, distinctRawIndex] using (hdata 0).2.2.1
    · simpa [idx, distinctRawIndex] using (hdata 1).2.2.1
    · simpa [idx, distinctRawIndex] using hextra_inner 0
    · simpa [idx, distinctRawIndex] using hextra_inner 1
  let I : Finset (Fin 15) := Finset.univ.filter (fun j => ‖p j‖ < b)
  have hIeq : I = Finset.univ \ boundarySet p b := by
    ext j
    simp only [I, boundarySet, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hj
      exact ne_of_lt hj
    · intro hj
      exact lt_of_le_of_ne (hpack.1 j) hj
  have hIcard : I.card = 6 := by
    rw [hIeq, Finset.card_sdiff_of_subset (by simp), Finset.card_univ, hK9]
    rfl
  have hsub : Finset.univ.image idx ⊆ I := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simpa [I] using hidx_inner i
  have himage : Finset.univ.image idx = I := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ hidxinj, hIcard]
    simp
  have hidx_cover (j : Fin 15) (hj : ‖p j‖ < b) :
      ∃ i, idx (src i) = j := by
    have hmem : j ∈ Finset.univ.image idx := by
      rw [himage]
      simpa [I] using hj
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hmem
    obtain ⟨i, hi⟩ := hsurj r
    exact ⟨i, by rw [hi]; exact hr⟩
  exact ⟨sorted, φ, w, hsepSorted, hmono, harg, hfirst, hlast,
    hcountA, hcountH, hcountL, hA, hH, hL,
    ⟨apos, hpos, hAlabel, hHlabel, hqA, hqH,
      (by intro c d heq; fin_cases c <;> fin_cases d <;>
        simp_all [hApos_ne]),
      (by intro c d heq; fin_cases c <;> fin_cases d <;>
        simp_all [hHpos_ne]), hadj⟩,
    hmatch, hbudget, ⟨fun i => idx (src i),
      fun i j h => hsrc (hidxinj h), fun _ => rfl,
      fun i => hidx_inner (src i), hidx_cover⟩⟩

end CP15
