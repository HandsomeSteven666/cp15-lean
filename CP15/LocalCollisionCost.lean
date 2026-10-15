import CP15.SevenBoundaryContacts
import CP15.TouchingCount
import CP15.TrigonometricPolynomialBounds

namespace CP15

set_option maxHeartbeats 0

/-- A uniformly small offset for every genuine contact below the radial
cap. This applies to low as well as high touching centers. -/
theorem capped_contact_offset_lt_13_div_20 (b r δ : ℝ)
    (hb : (16 / 5 : ℝ) < b) (hr : 0 < r) (hD : r < D b)
    (hd0 : 0 ≤ δ) (hdpi : δ ≤ Real.pi)
    (hlaw : 2 * r * b * Real.cos δ = b ^ 2 + r ^ 2 - 4) :
    δ < 13 / 20 := by
  have hb0 : 0 < b := by linarith
  have hα := contact_alignment_strict b r hb0 hD
  have hscaled : 2 * r * (b ^ 2 - 2) <
      2 * r * (b ^ 2 * Real.cos δ) := by nlinarith
  have hc : b ^ 2 - 2 < b ^ 2 * Real.cos δ :=
    (mul_lt_mul_iff_of_pos_left (by positivity : 0 < 2 * r)).mp hscaled
  have hcLo : (103 / 128 : ℝ) < Real.cos δ := by
    by_contra hn
    have hprod : 0 ≤ b ^ 2 * (103 / 128 - Real.cos δ) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  by_contra hn
  have hbig : (13 / 20 : ℝ) ≤ δ := le_of_not_gt hn
  have hcHi := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0 : ℝ) ≤ 13 / 20) hdpi hbig
  have hpoly := cos_taylor_four_upper (13 / 20) (by norm_num)
  norm_num at hpoly
  linarith

private theorem same_side_offsets_close (left right x y d e : ℝ)
    (hd : 0 ≤ d ∧ d ≤ 13 / 20) (he : 0 ≤ e ∧ e ≤ 13 / 20)
    (hpos : (x = left + d ∧ y = left + e) ∨
      (x = right - d ∧ y = right - e)) : |x - y| ≤ 13 / 20 := by
  apply abs_le.mpr
  rcases hpos with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    constructor <;> rw [hx, hy] <;> linarith [hd.1, hd.2, he.1, he.2]

/-- The complete local collision accounting rule. The finite contact
family may contain both endpoints, and its size is derived from actual
angle separation. No injective assignment of contacts to gaps is assumed. -/
theorem local_collision_extra_cost_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (left right β : ℝ) (θ δ : ι → ℝ)
    (hβ0 : 0 ≤ β) (hβ8 : β ≤ 4 / 5) (hcap : (13 / 10 : ℝ) ≤ 4 / 5 + β)
    (hbase : β ≤ right - left)
    (hδ : ∀ i ∈ s, 0 ≤ δ i ∧ δ i ≤ 13 / 20)
    (hsupport : ∀ i ∈ s, 2 * δ i ≤ right - left)
    (hposition : ∀ i ∈ s, θ i = left + δ i ∨ θ i = right - δ i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (4 / 5 : ℝ) < |θ i - θ j|) :
    (∑ i ∈ s, max 0 (2 * δ i - β)) ≤ right - left - β := by
  classical
  let side : ι → Bool := fun i => if θ i = left + δ i then true else false
  have hsame (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s)
      (hpos : (θ i = left + δ i ∧ θ j = left + δ j) ∨
        (θ i = right - δ i ∧ θ j = right - δ j)) : i = j := by
    by_contra hn
    have hclose := same_side_offsets_close left right (θ i) (θ j) (δ i) (δ j)
      (hδ i hi) (hδ j hj) hpos
    linarith [hsep i hi j hj hn]
  have hinj : Set.InjOn side s := by
    intro i hi j hj heq
    by_cases hlefti : θ i = left + δ i
    · by_cases hleftj : θ j = left + δ j
      · exact hsame i hi j hj (Or.inl ⟨hlefti, hleftj⟩)
      · simp [side, hlefti, hleftj] at heq
    · by_cases hleftj : θ j = left + δ j
      · simp [side, hlefti, hleftj] at heq
      · exact hsame i hi j hj (Or.inr
          ⟨(hposition i hi).resolve_left hlefti, (hposition j hj).resolve_left hleftj⟩)
  have hcard : s.card ≤ 2 := by
    have hc := Finset.card_le_card (show s.image side ⊆ (Finset.univ : Finset Bool) by
      intro i _
      exact Finset.mem_univ i)
    rw [Finset.card_image_of_injOn hinj] at hc
    simpa using hc
  by_cases hzero : s.card = 0
  · have hempty := Finset.card_eq_zero.mp hzero
    subst s
    simp only [Finset.sum_empty]
    linarith
  by_cases hone : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    simp only [Finset.sum_singleton]
    apply max_le
    · linarith
    · linarith [hsupport i (by simp)]
  have htwo : s.card = 2 := by omega
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp htwo
  have hi : i ∈ ({i, j} : Finset ι) := by simp
  have hj : j ∈ ({i, j} : Finset ι) := by simp
  have hspread : δ i + δ j + 4 / 5 ≤ right - left := by
    rcases hposition i hi with hil | hir <;> rcases hposition j hj with hjl | hjr
    · exact False.elim (hij (hsame i hi j hj (Or.inl ⟨hil, hjl⟩)))
    · have horder : θ i ≤ θ j := by rw [hil, hjr]; linarith [hsupport i hi, hsupport j hj]
      have habs : |θ i - θ j| = θ j - θ i := by
        rw [abs_of_nonpos (by linarith)]
        ring
      have hs := hsep i hi j hj hij
      rw [habs, hil, hjr] at hs
      linarith
    · have horder : θ j ≤ θ i := by rw [hir, hjl]; linarith [hsupport i hi, hsupport j hj]
      have habs : |θ i - θ j| = θ i - θ j := abs_of_nonneg (by linarith)
      have hs := hsep i hi j hj hij
      rw [habs, hir, hjl] at hs
      linarith
    · exact False.elim (hij (hsame i hi j hj (Or.inr ⟨hir, hjr⟩)))
  rw [Finset.sum_pair hij]
  by_cases hiLow : 2 * δ i ≤ β <;> by_cases hjLow : 2 * δ j ≤ β
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    linarith [hsupport j hj]
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    linarith [hsupport i hi]
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    linarith [(hδ i hi).2, (hδ j hj).2]

end CP15
