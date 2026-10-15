import CP15.K10m1WordCertificate
import CP15.RationalFullAngle
import CP15.OneCoreBounds

namespace CP15

set_option maxHeartbeats 0

theorem k10_YY_data (i : Fin 12) (j : Fin 12) :
    k10YYUnits i j = 0 ∨
      (k10TouchHi i : ℝ) + k10TouchHi j < 2 ∨
      (0 < (k10TouchLo i : ℝ) ∧ 0 < (k10TouchLo j : ℝ) ∧
        0 ≤ (k10YYUnits i j : ℝ) / 10000 ∧ (k10YYUnits i j : ℝ) / 10000 ≤ 31415 / 10000 ∧
        (k10YYCos i j : ℝ) < 1 - 2 * sinNineUpper ((k10YYUnits i j : ℝ) / 20000) ^ 2 ∧
        pairExpr (k10TouchLo i) (k10TouchLo j) (k10YYCos i j) < 4 ∧
        pairExpr (k10TouchLo i) (k10TouchHi j) (k10YYCos i j) < 4 ∧
        pairExpr (k10TouchHi i) (k10TouchLo j) (k10YYCos i j) < 4 ∧
        pairExpr (k10TouchHi i) (k10TouchHi j) (k10YYCos i j) < 4) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k10YYUnits, k10YYCos, k10TouchLo, k10TouchHi, k10TouchLo, k10TouchHi, pairExpr, sinNineUpper]

theorem k10_YY_angle_lower (x y : Plane) (g : ℝ) (i : Fin 12) (j : Fin 12)
    (hiLo : (k10TouchLo i : ℝ) ≤ ‖x‖) (hiHi : ‖x‖ ≤ k10TouchHi i)
    (hjLo : (k10TouchLo j : ℝ) ≤ ‖y‖) (hjHi : ‖y‖ ≤ k10TouchHi j)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (k10YYUnits i j : ℝ) / 10000 ≤ g := by
  rcases k10_YY_data i j with hz | himp | ⟨hri, hrj, hk0, hkπ, hc, hll, hlh, hhl, hhh⟩
  · simpa [hz] using hg
  · have hn := norm_sub_le x y
    rw [← dist_eq_norm] at hn
    linarith
  · have hkπ' : (k10YYUnits i j : ℝ) / 10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
    have hcosLower : (k10YYCos i j : ℝ) < Real.cos ((k10YYUnits i j : ℝ) / 10000) := by
      apply cos_full_radians_lower_of_certificate _ _ hk0 hkπ'
      convert hc using 1 <;> congr 2 <;> ring
    exact (directed_pair_box_full_radian_gt x y g ((k10YYUnits i j : ℝ) / 10000)
      (k10YYCos i j) (k10TouchLo i) (k10TouchHi i) (k10TouchLo j) (k10TouchHi j)
      hri hrj hiLo hiHi hjLo hjHi hsep hcos hg hk0 hkπ' hcosLower hll hlh hhl hhh).le

theorem k10_AY_data (i : Fin 7) (j : Fin 12) :
    k10AYUnits i j = 0 ∨
      (k10CoreHi i : ℝ) + k10TouchHi j < 2 ∨
      (0 < (k10CoreLo i : ℝ) ∧ 0 < (k10TouchLo j : ℝ) ∧
        0 ≤ (k10AYUnits i j : ℝ) / 10000 ∧ (k10AYUnits i j : ℝ) / 10000 ≤ 31415 / 10000 ∧
        (k10AYCos i j : ℝ) < 1 - 2 * sinNineUpper ((k10AYUnits i j : ℝ) / 20000) ^ 2 ∧
        pairExpr (k10CoreLo i) (k10TouchLo j) (k10AYCos i j) < 4 ∧
        pairExpr (k10CoreLo i) (k10TouchHi j) (k10AYCos i j) < 4 ∧
        pairExpr (k10CoreHi i) (k10TouchLo j) (k10AYCos i j) < 4 ∧
        pairExpr (k10CoreHi i) (k10TouchHi j) (k10AYCos i j) < 4) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k10AYUnits, k10AYCos, k10CoreLo, k10CoreHi, k10TouchLo, k10TouchHi, pairExpr, sinNineUpper]

theorem k10_AY_angle_lower (x y : Plane) (g : ℝ) (i : Fin 7) (j : Fin 12)
    (hiLo : (k10CoreLo i : ℝ) ≤ ‖x‖) (hiHi : ‖x‖ ≤ k10CoreHi i)
    (hjLo : (k10TouchLo j : ℝ) ≤ ‖y‖) (hjHi : ‖y‖ ≤ k10TouchHi j)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (k10AYUnits i j : ℝ) / 10000 ≤ g := by
  rcases k10_AY_data i j with hz | himp | ⟨hri, hrj, hk0, hkπ, hc, hll, hlh, hhl, hhh⟩
  · simpa [hz] using hg
  · have hn := norm_sub_le x y
    rw [← dist_eq_norm] at hn
    linarith
  · have hkπ' : (k10AYUnits i j : ℝ) / 10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
    have hcosLower : (k10AYCos i j : ℝ) < Real.cos ((k10AYUnits i j : ℝ) / 10000) := by
      apply cos_full_radians_lower_of_certificate _ _ hk0 hkπ'
      convert hc using 1 <;> congr 2 <;> ring
    exact (directed_pair_box_full_radian_gt x y g ((k10AYUnits i j : ℝ) / 10000)
      (k10AYCos i j) (k10CoreLo i) (k10CoreHi i) (k10TouchLo j) (k10TouchHi j)
      hri hrj hiLo hiHi hjLo hjHi hsep hcos hg hk0 hkπ' hcosLower hll hlh hhl hhh).le

theorem k10_core_bin_cover (r : ℝ) (hlo : (1 / 4 : ℝ) ≤ r)
    (hhi : r ≤ 1) :
    ∃ i : Fin 7, (k10CoreLo i : ℝ) ≤ r ∧ r ≤ k10CoreHi i := by
  by_cases h0 : r ≤ (3 / 10 : ℝ)
  · refine ⟨0, ?_, ?_⟩ <;> norm_num [k10CoreLo, k10CoreHi] <;> linarith
  ·
    by_cases h1 : r ≤ (7 / 20 : ℝ)
    · refine ⟨1, ?_, ?_⟩ <;> norm_num [k10CoreLo, k10CoreHi] <;> linarith
    ·
      by_cases h2 : r ≤ (2 / 5 : ℝ)
      · refine ⟨2, ?_, ?_⟩ <;> norm_num [k10CoreLo, k10CoreHi] <;> linarith
      ·
        by_cases h3 : r ≤ (3 / 5 : ℝ)
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [k10CoreLo, k10CoreHi] <;> linarith
        ·
          by_cases h4 : r ≤ (4 / 5 : ℝ)
          · refine ⟨4, ?_, ?_⟩ <;> norm_num [k10CoreLo, k10CoreHi] <;> linarith
          ·
            by_cases h5 : r ≤ (9 / 10 : ℝ)
            · refine ⟨5, ?_, ?_⟩ <;> norm_num [k10CoreLo, k10CoreHi] <;> linarith
            ·
              refine ⟨6, ?_, ?_⟩ <;> norm_num [k10CoreLo, k10CoreHi] <;> linarith

theorem k10_touch_bin_cover (r : ℝ) (hlo : (123 / 100 : ℝ) ≤ r)
    (hhi : r ≤ 4771 / 2000) :
    ∃ i : Fin 12, (k10TouchLo i : ℝ) ≤ r ∧ r ≤ k10TouchHi i := by
  by_cases h0 : r ≤ (3 / 2 : ℝ)
  · refine ⟨0, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
  ·
    by_cases h1 : r ≤ (8 / 5 : ℝ)
    · refine ⟨1, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
    ·
      by_cases h2 : r ≤ (41 / 25 : ℝ)
      · refine ⟨2, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
      ·
        by_cases h3 : r ≤ (33 / 20 : ℝ)
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
        ·
          by_cases h4 : r ≤ (17 / 10 : ℝ)
          · refine ⟨4, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
          ·
            by_cases h5 : r ≤ (9 / 5 : ℝ)
            · refine ⟨5, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
            ·
              by_cases h6 : r ≤ (19 / 10 : ℝ)
              · refine ⟨6, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
              ·
                by_cases h7 : r ≤ (2 : ℝ)
                · refine ⟨7, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
                ·
                  by_cases h8 : r ≤ (21 / 10 : ℝ)
                  · refine ⟨8, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
                  ·
                    by_cases h9 : r ≤ (11 / 5 : ℝ)
                    · refine ⟨9, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
                    ·
                      by_cases h10 : r ≤ (23 / 10 : ℝ)
                      · refine ⟨10, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith
                      ·
                        refine ⟨11, ?_, ?_⟩ <;> norm_num [k10TouchLo, k10TouchHi] <;> linarith

theorem k10_touch_bin_extra_lower {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) (q : Fin 15) (hinner : ‖p q‖ < b)
    (htouch : TouchesOuter p b q) (i : Fin 12) (hlo : (k10TouchLo i : ℝ) ≤ ‖p q‖) :
    (k10ExtraUnits i : ℝ) / 10000 ≤
      max 0 (2 * contactAngle b ‖p q‖ - 57588 / 100000) := by
  have hgamma : (k10GammaUnits i : ℝ) / 10000 ≤ contactAngle b ‖p q‖ := by
    fin_cases i
    ·
      norm_num [k10GammaUnits]
      exact Real.arccos_nonneg _
    ·
      norm_num [k10GammaUnits]
      exact Real.arccos_nonneg _
    ·
      norm_num [k10GammaUnits]
      exact Real.arccos_nonneg _
    ·
      norm_num [k10GammaUnits]
      exact Real.arccos_nonneg _
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (33 / 20) (2937 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (17 / 10) (212 / 625) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (9 / 5) (509 / 1250) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (19 / 10) (2283 / 5000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (2) (4941 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (21 / 10) (5233 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (11 / 5) (5461 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k10GammaUnits, k10TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (23 / 10) (5639 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
  have hmax := le_max_right (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  have hnonneg := le_max_left (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  fin_cases i <;> norm_num [k10ExtraUnits, k10GammaUnits] at hgamma ⊢ <;> linarith

end CP15
