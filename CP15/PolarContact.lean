import CP15.OuterGapShort
import CP15.OuterContactAlgebra

open scoped InnerProductSpace

namespace CP15

/-- Real inner product in polar coordinates, valid even at the origin. -/
theorem polar_inner (x y : Plane) :
    ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ *
      Real.cos (polarArg x - polarArg y) := by
  have hxc : ‖x‖ * Real.cos (polarArg x) = x 0 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_cos_arg (planeComplex x)
  have hxs : ‖x‖ * Real.sin (polarArg x) = x 1 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_sin_arg (planeComplex x)
  have hyc : ‖y‖ * Real.cos (polarArg y) = y 0 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_cos_arg (planeComplex y)
  have hys : ‖y‖ * Real.sin (polarArg y) = y 1 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_sin_arg (planeComplex y)
  have hcoord : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  rw [hcoord, Real.cos_sub]
  calc
    x 0 * y 0 + x 1 * y 1 =
        (‖x‖ * Real.cos (polarArg x)) * (‖y‖ * Real.cos (polarArg y)) +
          (‖x‖ * Real.sin (polarArg x)) * (‖y‖ * Real.sin (polarArg y)) := by
      rw [hxc, hxs, hyc, hys]
    _ = ‖x‖ * ‖y‖ *
        (Real.cos (polarArg x) * Real.cos (polarArg y) +
          Real.sin (polarArg x) * Real.sin (polarArg y)) := by ring

/-- A contact to a boundary center at radius greater than two has positive
radial inner product. This also excludes an origin contact. -/
theorem inner_outer_contact_dot_pos (q z : Plane) (b : ℝ)
    (hb : 2 < b) (hz : ‖z‖ = b) (hcontact : dist q z = 2) :
    0 < ⟪q, z⟫_ℝ := by
  have h := contact_inner_formula q z b ‖q‖ rfl hz hcontact
  nlinarith [sq_nonneg ‖q‖]

theorem inner_outer_contact_cos_pos (q z : Plane) (b : ℝ)
    (hb : 2 < b) (hz : ‖z‖ = b) (hcontact : dist q z = 2) :
    0 < Real.cos (polarArg q - polarArg z) := by
  have hdot := inner_outer_contact_dot_pos q z b hb hz hcontact
  have hq : 0 < ‖q‖ := by
    by_contra hnot
    have hzero : q = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hnot) (norm_nonneg q))
    rw [hzero] at hdot
    simp at hdot
  rw [polar_inner q z, hz] at hdot
  by_contra hnot
  have hcos : Real.cos (polarArg q - polarArg z) ≤ 0 := le_of_not_gt hnot
  have hprod := mul_nonneg (mul_nonneg hq.le (by linarith : 0 ≤ b))
    (neg_nonneg.mpr hcos)
  nlinarith

/-- Contact support stated for arbitrary real lifts of the three polar
arguments. The cosine identities make branch-cut handling explicit. -/
theorem contact_gap_doubling_lift (q z w : Plane) (b s θq θz θw : ℝ)
    (hb : 0 < b) (hs : 0 < s) (hsD : s < D b)
    (hq : ‖q‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist q z = 2)
    (hclear : 2 ≤ dist q w) (houter : 2 ≤ dist z w)
    (hqz : Real.cos (polarArg q - polarArg z) = Real.cos (θq - θz))
    (hqw : Real.cos (polarArg q - polarArg w) = Real.cos (θq - θw))
    (hzw : Real.cos (polarArg z - polarArg w) = Real.cos (θz - θw))
    (hqside : θz ≤ θq) (hqhalf : θq - θz ≤ Real.pi)
    (hwside : θz ≤ θw) (hshort : θw - θz < Real.pi) :
    θq < θw ∧ 2 * (θq - θz) ≤ θw - θz := by
  let γ := θq - θz
  let Δ := θw - θz
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith
  have hΔ0 : 0 ≤ Δ := by dsimp [Δ]; linarith
  have hγπ : γ ≤ Real.pi := hqhalf
  have hΔπ : Δ ≤ Real.pi := hshort.le
  have hdot := contact_closer_than_outer_pair q z w b s hb hs.le hsD
    hq hz hw hcontact houter
  rw [polar_inner z w, polar_inner q z, hz, hw, hq, hzw, hqz] at hdot
  have heqzw : θz - θw = -Δ := by dsimp [Δ]; ring
  have heqqz : θq - θz = γ := rfl
  rw [heqzw, Real.cos_neg, heqqz] at hdot
  have hcoef : 0 < s * b * b := mul_pos (mul_pos hs hb) hb
  have hcos : Real.cos Δ < Real.cos γ := by
    apply (mul_lt_mul_iff_of_pos_left hcoef).mp
    nlinarith [hdot]
  have hγlt : γ < Δ := by
    by_contra hnot
    have hΔγ : Δ ≤ γ := le_of_not_gt hnot
    have hrev := Real.cos_le_cos_of_nonneg_of_le_pi hΔ0 hγπ hΔγ
    linarith
  have hqbefore : θq < θw := by dsimp [γ, Δ] at hγlt; linarith
  have hdot2 := contact_outer_dot_max q z w b hz hw hcontact hclear
  rw [polar_inner q w, polar_inner q z, hq, hw, hz, hqw, hqz] at hdot2
  have heqqw : θq - θw = -(Δ - γ) := by dsimp [Δ, γ]; ring
  rw [heqqw, Real.cos_neg, heqqz] at hdot2
  have hcos2 : Real.cos (Δ - γ) ≤ Real.cos γ :=
    (mul_le_mul_iff_of_pos_left (mul_pos hs hb)).mp (by nlinarith [hdot2])
  have hγle : γ ≤ Δ - γ :=
    (Real.strictAntiOn_cos.le_iff_ge
      (show Δ - γ ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show γ ∈ Set.Icc 0 Real.pi from ⟨hγ0, hγπ⟩)).mp hcos2
  refine ⟨hqbefore, ?_⟩
  dsimp [Δ, γ] at hγle ⊢
  linarith

theorem cos_sub_add_two_pi_right (a c : ℝ) :
    Real.cos (a - (c + 2 * Real.pi)) = Real.cos (a - c) := by
  convert Real.cos_sub_two_pi (a - c) using 1 <;> ring

theorem cos_add_two_pi_sub_left (a c : ℝ) :
    Real.cos ((a + 2 * Real.pi) - c) = Real.cos (a - c) := by
  convert Real.cos_add_two_pi (a - c) using 1 <;> ring

theorem cos_sub_two_pi_sub_left (a c : ℝ) :
    Real.cos ((a - 2 * Real.pi) - c) = Real.cos (a - c) := by
  convert Real.cos_sub_two_pi (a - c) using 1 <;> ring

/-- Support in a gap crossing the polar branch cut. The chosen real lift of
the inner angle is either its principal argument or that argument plus `2π`.
The lemma checks both possibilities; it does not select the appropriate one. -/
theorem contact_wrap_gap_doubling_lift (q z w : Plane) (b s θq : ℝ)
    (hb : 0 < b) (hs : 0 < s) (hsD : s < D b)
    (hq : ‖q‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist q z = 2)
    (hclear : 2 ≤ dist q w) (houter : 2 ≤ dist z w)
    (hlift : θq = polarArg q ∨ θq = polarArg q + 2 * Real.pi)
    (hqside : polarArg z ≤ θq)
    (hqhalf : θq - polarArg z ≤ Real.pi)
    (hwside : polarArg z ≤ polarArg w + 2 * Real.pi)
    (hshort : polarArg w + 2 * Real.pi - polarArg z < Real.pi) :
    θq < polarArg w + 2 * Real.pi ∧
      2 * (θq - polarArg z) ≤
        polarArg w + 2 * Real.pi - polarArg z := by
  have hqz : Real.cos (polarArg q - polarArg z) =
      Real.cos (θq - polarArg z) := by
    rcases hlift with h | h
    · rw [h]
    · rw [h, cos_add_two_pi_sub_left]
  have hqw : Real.cos (polarArg q - polarArg w) =
      Real.cos (θq - (polarArg w + 2 * Real.pi)) := by
    rcases hlift with h | h
    · rw [h, cos_sub_add_two_pi_right]
    · rw [h]
      congr 1
      ring
  have hzw : Real.cos (polarArg z - polarArg w) =
      Real.cos (polarArg z - (polarArg w + 2 * Real.pi)) := by
    rw [cos_sub_add_two_pi_right]
  exact contact_gap_doubling_lift q z w b s θq (polarArg z)
    (polarArg w + 2 * Real.pi) hb hs hsD hq hz hw hcontact
    hclear houter hqz hqw hzw hqside hqhalf hwside hshort

/-- Backward support for arbitrary angle lifts follows by reflecting all
three real angle coordinates. -/
theorem contact_gap_doubling_lift_backward (q z w : Plane) (b s θq θz θw : ℝ)
    (hb : 0 < b) (hs : 0 < s) (hsD : s < D b)
    (hq : ‖q‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist q z = 2)
    (hclear : 2 ≤ dist q w) (houter : 2 ≤ dist z w)
    (hqz : Real.cos (polarArg q - polarArg z) = Real.cos (θq - θz))
    (hqw : Real.cos (polarArg q - polarArg w) = Real.cos (θq - θw))
    (hzw : Real.cos (polarArg z - polarArg w) = Real.cos (θz - θw))
    (hqside : θq ≤ θz) (hqhalf : θz - θq ≤ Real.pi)
    (hwside : θw ≤ θz) (hshort : θz - θw < Real.pi) :
    θw < θq ∧ 2 * (θz - θq) ≤ θz - θw := by
  have hqz' : Real.cos (polarArg q - polarArg z) =
      Real.cos ((-θq) - (-θz)) := by
    rw [hqz]
    have heq : -θq - -θz = -(θq - θz) := by ring
    rw [heq, Real.cos_neg]
  have hqw' : Real.cos (polarArg q - polarArg w) =
      Real.cos ((-θq) - (-θw)) := by
    rw [hqw]
    have heq : -θq - -θw = -(θq - θw) := by ring
    rw [heq, Real.cos_neg]
  have hzw' : Real.cos (polarArg z - polarArg w) =
      Real.cos ((-θz) - (-θw)) := by
    rw [hzw]
    have heq : -θz - -θw = -(θz - θw) := by ring
    rw [heq, Real.cos_neg]
  have h := contact_gap_doubling_lift q z w b s (-θq) (-θz) (-θw)
    hb hs hsD hq hz hw hcontact hclear houter hqz' hqw' hzw'
    (by linarith) (by linarith) (by linarith) (by linarith)
  constructor <;> linarith [h.1, h.2]

/-- Backward support in the boundary gap that crosses the polar branch cut. -/
theorem contact_wrap_gap_doubling_lift_backward (q z w : Plane) (b s θq : ℝ)
    (hb : 0 < b) (hs : 0 < s) (hsD : s < D b)
    (hq : ‖q‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist q z = 2)
    (hclear : 2 ≤ dist q w) (houter : 2 ≤ dist z w)
    (hlift : θq = polarArg q ∨ θq = polarArg q + 2 * Real.pi)
    (hqside : θq ≤ polarArg z + 2 * Real.pi)
    (hqhalf : polarArg z + 2 * Real.pi - θq ≤ Real.pi)
    (hwside : polarArg w ≤ polarArg z + 2 * Real.pi)
    (hshort : polarArg z + 2 * Real.pi - polarArg w < Real.pi) :
    polarArg w < θq ∧
      2 * (polarArg z + 2 * Real.pi - θq) ≤
        polarArg z + 2 * Real.pi - polarArg w := by
  have hqz : Real.cos (polarArg q - polarArg z) =
      Real.cos (θq - (polarArg z + 2 * Real.pi)) := by
    rcases hlift with h | h
    · rw [h, cos_sub_add_two_pi_right]
    · rw [h]
      congr 1
      ring
  have hqw : Real.cos (polarArg q - polarArg w) =
      Real.cos (θq - polarArg w) := by
    rcases hlift with h | h
    · rw [h]
    · rw [h, cos_add_two_pi_sub_left]
  have hzw : Real.cos (polarArg z - polarArg w) =
      Real.cos ((polarArg z + 2 * Real.pi) - polarArg w) := by
    rw [cos_add_two_pi_sub_left]
  exact contact_gap_doubling_lift_backward q z w b s θq
    (polarArg z + 2 * Real.pi) (polarArg w)
    hb hs hsD hq hz hw hcontact hclear houter
    hqz hqw hzw hqside hqhalf hwside hshort

/-- A positive cosine between two principal polar arguments admits a real
lift of their difference into the open half-circle. The three possibilities
cover the branch cut exactly. -/
theorem positive_cos_has_short_lift (a c : ℝ)
    (ha : -Real.pi < a ∧ a ≤ Real.pi)
    (hc : -Real.pi < c ∧ c ≤ Real.pi)
    (hcos : 0 < Real.cos (a - c)) :
    |a - c| < Real.pi / 2 ∨
      |(a + 2 * Real.pi) - c| < Real.pi / 2 ∨
      |(a - 2 * Real.pi) - c| < Real.pi / 2 := by
  let d := a - c
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdlo : -(2 * Real.pi) < d := by dsimp [d]; linarith [ha.1, hc.2]
  have hdhi : d < 2 * Real.pi := by dsimp [d]; linarith [ha.2, hc.1]
  by_cases hd0 : 0 ≤ d
  · by_cases hdsmall : d < Real.pi / 2
    · left
      apply abs_lt.mpr
      dsimp [d] at hd0 hdsmall ⊢
      constructor <;> linarith
    · have hdlarge : 3 * Real.pi / 2 < d := by
        by_contra hnot
        have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le
          (le_of_not_gt hdsmall) (by linarith [le_of_not_gt hnot])
        dsimp [d] at hnonpos hcos
        linarith
      right; right
      apply abs_lt.mpr
      dsimp [d] at hdlarge hdhi ⊢
      constructor <;> linarith
  · have hdneg : d < 0 := lt_of_not_ge hd0
    by_cases hdsmall : -d < Real.pi / 2
    · left
      apply abs_lt.mpr
      dsimp [d] at hdneg hdsmall ⊢
      constructor <;> linarith
    · have hdlarge : 3 * Real.pi / 2 < -d := by
        by_contra hnot
        have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le
          (le_of_not_gt hdsmall) (by linarith [le_of_not_gt hnot])
        have hcos' : 0 < Real.cos (-d) := by rw [Real.cos_neg]; exact hcos
        linarith
      right; left
      apply abs_lt.mpr
      dsimp [d] at hdlarge hdlo ⊢
      constructor <;> linarith

theorem inner_outer_contact_has_short_lift (q z : Plane) (b : ℝ)
    (hb : 2 < b) (hz : ‖z‖ = b) (hcontact : dist q z = 2) :
    |polarArg q - polarArg z| < Real.pi / 2 ∨
      |(polarArg q + 2 * Real.pi) - polarArg z| < Real.pi / 2 ∨
      |(polarArg q - 2 * Real.pi) - polarArg z| < Real.pi / 2 := by
  exact positive_cos_has_short_lift (polarArg q) (polarArg z)
    (polarArg_range q) (polarArg_range z)
    (inner_outer_contact_cos_pos q z b hb hz hcontact)

/-- In the ordered situation `z, q, w`, contact with `z` and clearance
from `w` force the outer angular gap to cover twice the contact offset.
This is the analytic implication only; choosing the neighboring `w` is a
separate finite-order step. -/
theorem contact_gap_doubling (q z w : Plane) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hq : ‖q‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist q z = 2) (hclear : 2 ≤ dist q w)
    (horder : polarArg z ≤ polarArg q ∧ polarArg q ≤ polarArg w)
    (hshort : polarArg w - polarArg z < Real.pi) :
    2 * (polarArg q - polarArg z) ≤ polarArg w - polarArg z := by
  let γ := polarArg q - polarArg z
  let Δ := polarArg w - polarArg z
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith [horder.1]
  have hΔγ : 0 ≤ Δ - γ := by dsimp [Δ, γ]; linarith [horder.2]
  have hγπ : γ ≤ Real.pi := by dsimp [γ, Δ] at *; linarith
  have hΔγπ : Δ - γ ≤ Real.pi := by dsimp [γ, Δ] at *; linarith
  have hdot := contact_outer_dot_max q z w b hz hw hcontact hclear
  rw [polar_inner q w, polar_inner q z, hq, hw, hz] at hdot
  have hcos : Real.cos (Δ - γ) ≤ Real.cos γ := by
    have heqw : polarArg q - polarArg w = -(Δ - γ) := by dsimp [Δ, γ]; ring
    have heqz : polarArg q - polarArg z = γ := rfl
    rw [heqw, Real.cos_neg, heqz] at hdot
    have hsb : 0 < s * b := mul_pos hs hb
    exact (mul_le_mul_iff_of_pos_left hsb).mp (by nlinarith [hdot])
  have hγle : γ ≤ Δ - γ :=
    (Real.strictAntiOn_cos.le_iff_ge
      (show Δ - γ ∈ Set.Icc 0 Real.pi from ⟨hΔγ, hΔγπ⟩)
      (show γ ∈ Set.Icc 0 Real.pi from ⟨hγ0, hγπ⟩)).mp hcos
  dsimp [Δ, γ] at hγle ⊢
  linarith

/-- The strict radial cap supplies the ordering premise of the previous
lemma: a contacted inner center on the forward half-circle must occur before
the next separated outer center in any short forward arc. -/
theorem contact_gap_doubling_from_cap (q z w : Plane) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s) (hsD : s < D b)
    (hq : ‖q‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist q z = 2)
    (hclear : 2 ≤ dist q w) (houter : 2 ≤ dist z w)
    (hqside : polarArg z ≤ polarArg q)
    (hqhalf : polarArg q - polarArg z ≤ Real.pi)
    (hwside : polarArg z ≤ polarArg w)
    (hshort : polarArg w - polarArg z < Real.pi) :
    polarArg q < polarArg w ∧
      2 * (polarArg q - polarArg z) ≤ polarArg w - polarArg z := by
  let γ := polarArg q - polarArg z
  let Δ := polarArg w - polarArg z
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith
  have hΔ0 : 0 ≤ Δ := by dsimp [Δ]; linarith
  have hγπ : γ ≤ Real.pi := hqhalf
  have hΔπ : Δ ≤ Real.pi := hshort.le
  have hdot := contact_closer_than_outer_pair q z w b s hb hs.le hsD
    hq hz hw hcontact houter
  rw [polar_inner z w, polar_inner q z, hz, hw, hq] at hdot
  have heqzw : polarArg z - polarArg w = -Δ := by dsimp [Δ]; ring
  have heqqz : polarArg q - polarArg z = γ := rfl
  rw [heqzw, Real.cos_neg, heqqz] at hdot
  have hcoef : 0 < s * b * b := mul_pos (mul_pos hs hb) hb
  have hcos : Real.cos Δ < Real.cos γ := by
    apply (mul_lt_mul_iff_of_pos_left hcoef).mp
    nlinarith [hdot]
  have hγlt : γ < Δ := by
    by_contra hnot
    have hΔγ : Δ ≤ γ := le_of_not_gt hnot
    have hrev := Real.cos_le_cos_of_nonneg_of_le_pi hΔ0 hγπ hΔγ
    linarith
  have hqbefore : polarArg q < polarArg w := by dsimp [γ, Δ] at hγlt; linarith
  refine ⟨hqbefore, ?_⟩
  exact contact_gap_doubling q z w b s hb hs hq hz hw hcontact hclear
    ⟨hqside, hqbefore.le⟩ hshort

/-- Indexed packing version. An inner point contacting a boundary point
cannot be the origin when `b > 2`; no origin exception is left implicit. -/
theorem packing_contact_gap_doubling (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (i j k : Fin 15)
    (hi : ‖p i‖ < b) (hj : ‖p j‖ = b) (hk : ‖p k‖ = b)
    (hjk : j ≠ k) (hcontact : dist (p i) (p j) = 2)
    (hqside : polarArg (p j) ≤ polarArg (p i))
    (hqhalf : polarArg (p i) - polarArg (p j) ≤ Real.pi)
    (hwside : polarArg (p j) ≤ polarArg (p k))
    (hshort : polarArg (p k) - polarArg (p j) < Real.pi) :
    polarArg (p i) < polarArg (p k) ∧
      2 * (polarArg (p i) - polarArg (p j)) ≤
        polarArg (p k) - polarArg (p j) := by
  have hne : p i ≠ 0 := by
    intro hzero
    have hd : dist (p i) (p j) = b := by
      rw [hzero, dist_zero_left, ← hj]
    linarith
  have hs : 0 < ‖p i‖ := norm_pos_iff.mpr hne
  have hik : i ≠ k := by
    intro heq
    rw [heq, hk] at hi
    exact (lt_irrefl b hi)
  exact contact_gap_doubling_from_cap (p i) (p j) (p k) b ‖p i‖
    (by linarith) hs (hD i hi) rfl hj hk hcontact
    (hsep i k hik) (hsep j k hjk)
    hqside hqhalf hwside hshort

/-- A forward inner-outer contact charges the immediately following gap in
the verified polar order. The forward-side premise is explicit; the global
step assigning every selected blocker to one of its two sides is separate. -/
theorem ordered_adjacent_contact_gap_doubling (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card)
    (hu : u.val + 1 < (boundaryAngles p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hforward : polarArg (p j) ≤ polarArg (p i))
    (hhalf : polarArg (p i) - polarArg (p j) ≤ Real.pi) :
    polarArg (p i) <
      (boundaryAngles p b).orderEmbOfFin rfl ⟨u.val + 1, hu⟩ ∧
      2 * (polarArg (p i) - polarArg (p j)) ≤
        (boundaryAngles p b).orderEmbOfFin rfl ⟨u.val + 1, hu⟩ -
          (boundaryAngles p b).orderEmbOfFin rfl u := by
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  let v : Fin s.card := ⟨u.val + 1, hu⟩
  have hv : e v ∈ s := Finset.orderEmbOfFin_mem s rfl v
  obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e v)).mp hv
  have huv : u < v := by
    change u.val < u.val + 1
    omega
  have hlt : e u < e v := e.strictMono huv
  have hjw : j ≠ w.val := by
    intro heq
    rw [heq] at hmatch
    linarith
  have hshort := ordered_boundary_adjacent_gap_lt_pi p b
    (by linarith) hbB hsep hK u hu
  have hresult := packing_contact_gap_doubling p b hb hsep hD
    i j w.val hi hj w.property hjw hcontact
    hforward hhalf (by dsimp [e] at hlt; linarith [hmatch, hw])
    (by simpa [s, e, v, hmatch, hw] using hshort)
  simpa only [hmatch, hw, s, e, v] using hresult

/-- Reverse-oriented counterpart: a contact on the backward side of `z`
charges the gap to the preceding outer point `w`. -/
theorem contact_gap_doubling_backward_from_cap (q z w : Plane) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s) (hsD : s < D b)
    (hq : ‖q‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist q z = 2)
    (hclear : 2 ≤ dist q w) (houter : 2 ≤ dist z w)
    (hqside : polarArg q ≤ polarArg z)
    (hqhalf : polarArg z - polarArg q ≤ Real.pi)
    (hwside : polarArg w ≤ polarArg z)
    (hshort : polarArg z - polarArg w < Real.pi) :
    polarArg w < polarArg q ∧
      2 * (polarArg z - polarArg q) ≤ polarArg z - polarArg w := by
  let γ := polarArg z - polarArg q
  let Δ := polarArg z - polarArg w
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith
  have hΔ0 : 0 ≤ Δ := by dsimp [Δ]; linarith
  have hγπ : γ ≤ Real.pi := hqhalf
  have hΔπ : Δ ≤ Real.pi := hshort.le
  have hdot := contact_closer_than_outer_pair q z w b s hb hs.le hsD
    hq hz hw hcontact houter
  rw [polar_inner z w, polar_inner q z, hz, hw, hq] at hdot
  have heqzw : polarArg z - polarArg w = Δ := rfl
  have heqqz : polarArg q - polarArg z = -γ := by dsimp [γ]; ring
  rw [heqzw, heqqz, Real.cos_neg] at hdot
  have hcoef : 0 < s * b * b := mul_pos (mul_pos hs hb) hb
  have hcos : Real.cos Δ < Real.cos γ := by
    apply (mul_lt_mul_iff_of_pos_left hcoef).mp
    nlinarith [hdot]
  have hγlt : γ < Δ := by
    by_contra hnot
    have hΔγ : Δ ≤ γ := le_of_not_gt hnot
    have hrev := Real.cos_le_cos_of_nonneg_of_le_pi hΔ0 hγπ hΔγ
    linarith
  have hqafter : polarArg w < polarArg q := by dsimp [γ, Δ] at hγlt; linarith
  have hdot2 := contact_outer_dot_max q z w b hz hw hcontact hclear
  rw [polar_inner q w, polar_inner q z, hq, hw, hz] at hdot2
  have heqqw : polarArg q - polarArg w = Δ - γ := by dsimp [Δ, γ]; ring
  rw [heqqw, heqqz, Real.cos_neg] at hdot2
  have hcos2 : Real.cos (Δ - γ) ≤ Real.cos γ := by
    exact (mul_le_mul_iff_of_pos_left (mul_pos hs hb)).mp (by nlinarith [hdot2])
  have hγle : γ ≤ Δ - γ :=
    (Real.strictAntiOn_cos.le_iff_ge
      (show Δ - γ ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show γ ∈ Set.Icc 0 Real.pi from ⟨hγ0, hγπ⟩)).mp hcos2
  refine ⟨hqafter, ?_⟩
  dsimp [Δ, γ] at hγle ⊢
  linarith

theorem packing_contact_gap_doubling_backward (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (i j k : Fin 15)
    (hi : ‖p i‖ < b) (hj : ‖p j‖ = b) (hk : ‖p k‖ = b)
    (hjk : j ≠ k) (hcontact : dist (p i) (p j) = 2)
    (hqside : polarArg (p i) ≤ polarArg (p j))
    (hqhalf : polarArg (p j) - polarArg (p i) ≤ Real.pi)
    (hwside : polarArg (p k) ≤ polarArg (p j))
    (hshort : polarArg (p j) - polarArg (p k) < Real.pi) :
    polarArg (p k) < polarArg (p i) ∧
      2 * (polarArg (p j) - polarArg (p i)) ≤
        polarArg (p j) - polarArg (p k) := by
  have hne : p i ≠ 0 := by
    intro hzero
    have hd : dist (p i) (p j) = b := by
      rw [hzero, dist_zero_left, ← hj]
    linarith
  have hs : 0 < ‖p i‖ := norm_pos_iff.mpr hne
  have hik : i ≠ k := by
    intro heq
    rw [heq, hk] at hi
    exact (lt_irrefl b hi)
  exact contact_gap_doubling_backward_from_cap (p i) (p j) (p k) b ‖p i‖
    (by linarith) hs (hD i hi) rfl hj hk hcontact
    (hsep i k hik) (hsep j k hjk)
    hqside hqhalf hwside hshort

/-- The backward adjacent-gap support theorem for the verified boundary
order, with explicit assumptions locating the contact on this side. -/
theorem ordered_previous_contact_gap_doubling (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card) (hu : 0 < u.val)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hbackward : polarArg (p i) ≤ polarArg (p j))
    (hhalf : polarArg (p j) - polarArg (p i) ≤ Real.pi) :
    (boundaryAngles p b).orderEmbOfFin rfl
      ⟨u.val - 1, by omega⟩ < polarArg (p i) ∧
      2 * (polarArg (p j) - polarArg (p i)) ≤
        (boundaryAngles p b).orderEmbOfFin rfl u -
          (boundaryAngles p b).orderEmbOfFin rfl
            ⟨u.val - 1, by omega⟩ := by
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  let v : Fin s.card := ⟨u.val - 1, by
    have hu' : u.val < s.card := u.isLt
    omega⟩
  have hv : e v ∈ s := Finset.orderEmbOfFin_mem s rfl v
  obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e v)).mp hv
  have huv : v < u := by
    change u.val - 1 < u.val
    omega
  have hlt : e v < e u := e.strictMono huv
  have hjw : j ≠ w.val := by
    intro heq
    rw [heq] at hmatch
    linarith
  have hvsucc : v.val + 1 < s.card := by
    change u.val - 1 + 1 < s.card
    have hu' : u.val < s.card := u.isLt
    omega
  have hshort' := ordered_boundary_adjacent_gap_lt_pi p b
    (by linarith) hbB hsep hK v hvsucc
  have hvsucc_eq : (⟨v.val + 1, hvsucc⟩ : Fin s.card) = u := by
    apply Fin.ext
    change u.val - 1 + 1 = u.val
    omega
  rw [hvsucc_eq] at hshort'
  have hresult := packing_contact_gap_doubling_backward p b hb hsep hD
    i j w.val hi hj w.property hjw hcontact
    hbackward hhalf (by dsimp [e] at hlt; linarith [hmatch, hw])
    (by simpa [s, e, v, hmatch, hw] using hshort')
  simpa only [hmatch, hw, s, e, v] using hresult

end CP15
