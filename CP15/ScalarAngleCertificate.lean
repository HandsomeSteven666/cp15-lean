import CP15.RationalFullAngle
import CP15.LocalAlternatingClosed
import CP15.CandidateFineBounds
import CP15.RationalTaylorFourteen

namespace CP15

set_option maxHeartbeats 0

def ratContactCos (a b : ℚ) : ℚ := (a ^ 2 + b ^ 2 - 4) / (2 * a * b)
def ratCosFourteen (t : ℚ) : ℚ :=
  1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 -
    t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200

theorem ratContactCos_cast (a b : ℚ) :
    (ratContactCos a b : ℝ) = contactCos a b := by
  simp [ratContactCos, contactCos]

theorem ratCosFourteen_cast_lower (t : ℚ) (ht : 0 ≤ t) :
    (ratCosFourteen t : ℝ) ≤ Real.cos t := by
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
  simpa [ratCosFourteen] using cos_taylor_fourteen_lower (t : ℝ) ht'

/-- Exact rational arithmetic produces a scalar angle certificate. A zero
bound is valid even outside the non-clamped triangle domain. -/
def scalarAngleCheck (a b : ℚ) (k unit : ℕ) : Bool :=
  decide (k = 0 ∨ (0 < unit ∧ (k : ℚ) / unit ≤ 31415 / 10000 ∧
    ratContactCos a b < ratCosFourteen ((k : ℚ) / unit)))

theorem scalarAngleCheck_sound (a b : ℚ) (k unit : ℕ)
    (hc : scalarAngleCheck a b k unit = true) (hunit : 0 < unit) :
    (k : ℝ) / unit ≤ contactAngle a b := by
  have hcheck : k = 0 ∨ (0 < unit ∧ (k : ℚ) / unit ≤ 31415 / 10000 ∧
      ratContactCos a b < ratCosFourteen ((k : ℚ) / unit)) := by
    simpa [scalarAngleCheck] using hc
  rcases hcheck with hz | ⟨_, hk, hcos⟩
  · simp only [hz, Nat.cast_zero, zero_div]
    exact Real.arccos_nonneg _
  have hu : (0 : ℝ) < unit := by exact_mod_cast hunit
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / unit := by positivity
  have hkq : (k : ℝ) / unit ≤ 31415 / 10000 := by
    have hh : (((k : ℚ) / unit : ℚ) : ℝ) ≤ ((31415 / 10000 : ℚ) : ℝ) := by
      exact_mod_cast hk
    simpa using hh
  have hkπ : (k : ℝ) / unit ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hcosActual : contactCos (a : ℝ) (b : ℝ) < Real.cos ((k : ℝ) / unit) := by
    have hh : (ratContactCos a b : ℝ) < (ratCosFourteen ((k : ℚ) / unit) : ℝ) := by
      exact_mod_cast hcos
    have hp := ratCosFourteen_cast_lower ((k : ℚ) / unit) (by positivity)
    simpa only [ratContactCos_cast, Rat.cast_div, Rat.cast_natCast] using hh.trans_le hp
  by_cases hlo : -1 ≤ contactCos (a : ℝ) (b : ℝ)
  · have hh := Real.arccos_lt_arccos hlo hcosActual (Real.cos_le_one _)
    rw [Real.arccos_cos hk0 hkπ] at hh
    exact hh.le
  · have hh : contactCos (a : ℝ) (b : ℝ) ≤ -1 := (lt_of_not_ge hlo).le
    change (k : ℝ) / unit ≤ Real.arccos _
    rw [Real.arccos_of_le_neg_one hh]
    exact hkπ

theorem contactCos_mono_annulus (r R s : ℝ)
    (hr : (123 / 100 : ℝ) ≤ r) (hR : r ≤ R) (hRu : R ≤ 9 / 4)
    (hs : (123 / 100 : ℝ) ≤ s) (hsu : s ≤ 9 / 4) :
    contactCos r s ≤ contactCos R s := by
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by linarith
  have hs0 : 0 < s := by linarith
  have hrsq : (123 / 100 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ (9 / 4 : ℝ) ^ 2 := by nlinarith
  have hprod : r ^ 2 ≤ R * r := by nlinarith
  have hf : 0 ≤ (R - r) * (R * r - s ^ 2 + 4) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hscaled := mul_nonneg (show 0 ≤ 2 * s by positivity) hf
  unfold contactCos
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * r * s)
    (by positivity : 0 < 2 * R * s)).2
  nlinarith

/-- On the complete K10 radial interval the pair angle is antitone in
either radius. The annulus width and triangle domain are checked. -/
theorem contactAngle_pair_upper_corner (r R s S : ℝ)
    (hr : (123 / 100 : ℝ) ≤ r) (hR : r ≤ R) (hRu : R ≤ 9 / 4)
    (hs : (123 / 100 : ℝ) ≤ s) (hS : s ≤ S) (hSu : S ≤ 9 / 4) :
    contactAngle R S ≤ contactAngle r s := by
  have h1 := contactCos_mono_annulus r R s hr hR hRu hs (hS.trans hSu)
  have h2 := contactCos_mono_annulus s S R hs hS hSu (hr.trans hR) hRu
  have heq (x y : ℝ) : contactCos x y = contactCos y x := by
    unfold contactCos
    congr 1 <;> ring
  rw [heq s R, heq S R] at h2
  exact Real.arccos_le_arccos (h1.trans h2)

theorem contactAngle_outer_lower_corner (b B l r : ℝ)
    (hb : 3 < b) (hbB : b ≤ B) (hBsq : 12 < B ^ 2)
    (hl : 0 < l) (hlr : l ≤ r) (hru : r ≤ 12 / 5) :
    contactAngle B l ≤ contactAngle b r := by
  have hb0 : 0 < b := by linarith
  have hB0 : 0 < B := by linarith
  have hr0 : 0 < r := by linarith
  have hmono : contactCos b r ≤ contactCos B r := by
    rcases eq_or_lt_of_le hbB with heq | hlt
    · rw [heq]
    · exact (contactCos_strict_mono_outer_radius b B r hb hlt hr0 hru).le
  have hlup : l ≤ 12 / 5 := hlr.trans hru
  have hf : 0 ≤ (r - l) * (B ^ 2 - 4 - l * r) := by
    apply mul_nonneg (by linarith)
    have hh : l * r ≤ (12 / 5 : ℝ) * (12 / 5 : ℝ) :=
      mul_le_mul hlup hru hr0.le (by norm_num)
    nlinarith
  have hscaled := mul_nonneg (show 0 ≤ 2 * B by positivity) hf
  have hanti : contactCos B r ≤ contactCos B l := by
    unfold contactCos
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * B * r)
      (by positivity : 0 < 2 * B * l)).2
    nlinarith
  exact Real.arccos_le_arccos (hmono.trans hanti)

end CP15
