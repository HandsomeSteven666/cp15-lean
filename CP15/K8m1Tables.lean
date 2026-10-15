import CP15.K8m1DiscreteData
import CP15.RationalFullAngle
import CP15.OneCoreBounds

namespace CP15

set_option maxHeartbeats 0

theorem k8m1_YY_data (i : Fin 12) (j : Fin 12) :
    k8m1YY i j = 0 ∨ (k8m1TouchHi i : ℝ) + k8m1TouchHi j < 2 ∨
      (0 < (k8m1TouchLo i : ℝ) ∧ 0 < (k8m1TouchLo j : ℝ) ∧
        0 ≤ (k8m1YY i j : ℝ) / 10000 ∧ (k8m1YY i j : ℝ) / 10000 ≤ 31415 / 10000 ∧
        (k8m1YYCos i j : ℝ) < 1 - 2 * sinNineUpper ((k8m1YY i j : ℝ) / 20000) ^ 2 ∧
        pairExpr (k8m1TouchLo i) (k8m1TouchLo j) (k8m1YYCos i j) < 4 ∧
        pairExpr (k8m1TouchLo i) (k8m1TouchHi j) (k8m1YYCos i j) < 4 ∧
        pairExpr (k8m1TouchHi i) (k8m1TouchLo j) (k8m1YYCos i j) < 4 ∧
        pairExpr (k8m1TouchHi i) (k8m1TouchHi j) (k8m1YYCos i j) < 4) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k8m1YY, k8m1YYCos, k8m1TouchLo, k8m1TouchHi, k8m1TouchLo, k8m1TouchHi, pairExpr, sinNineUpper]

theorem k8m1_YY_angle_lower (x y : Plane) (g : ℝ) (i : Fin 12) (j : Fin 12)
    (hiLo : (k8m1TouchLo i : ℝ) ≤ ‖x‖) (hiHi : ‖x‖ ≤ k8m1TouchHi i)
    (hjLo : (k8m1TouchLo j : ℝ) ≤ ‖y‖) (hjHi : ‖y‖ ≤ k8m1TouchHi j)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (k8m1YY i j : ℝ) / 10000 ≤ g := by
  rcases k8m1_YY_data i j with hz | himp | ⟨hri, hrj, hk0, hkπ, hc, hll, hlh, hhl, hhh⟩
  · simpa [hz] using hg
  · have hn := norm_sub_le x y
    rw [← dist_eq_norm] at hn
    linarith
  · have hkπ' : (k8m1YY i j : ℝ) / 10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
    have hcosLower : (k8m1YYCos i j : ℝ) < Real.cos ((k8m1YY i j : ℝ) / 10000) := by
      apply cos_full_radians_lower_of_certificate _ _ hk0 hkπ'
      convert hc using 1 <;> congr 2 <;> ring
    exact (directed_pair_box_full_radian_gt x y g ((k8m1YY i j : ℝ) / 10000)
      (k8m1YYCos i j) (k8m1TouchLo i) (k8m1TouchHi i) (k8m1TouchLo j) (k8m1TouchHi j)
      hri hrj hiLo hiHi hjLo hjHi hsep hcos hg hk0 hkπ' hcosLower hll hlh hhl hhh).le

theorem k8m1_AY_data (i : Fin 12) (j : Fin 12) :
    k8m1AY i j = 0 ∨ (k8m1CoreHi i : ℝ) + k8m1TouchHi j < 2 ∨
      (0 < (k8m1CoreLo i : ℝ) ∧ 0 < (k8m1TouchLo j : ℝ) ∧
        0 ≤ (k8m1AY i j : ℝ) / 10000 ∧ (k8m1AY i j : ℝ) / 10000 ≤ 31415 / 10000 ∧
        (k8m1AYCos i j : ℝ) < 1 - 2 * sinNineUpper ((k8m1AY i j : ℝ) / 20000) ^ 2 ∧
        pairExpr (k8m1CoreLo i) (k8m1TouchLo j) (k8m1AYCos i j) < 4 ∧
        pairExpr (k8m1CoreLo i) (k8m1TouchHi j) (k8m1AYCos i j) < 4 ∧
        pairExpr (k8m1CoreHi i) (k8m1TouchLo j) (k8m1AYCos i j) < 4 ∧
        pairExpr (k8m1CoreHi i) (k8m1TouchHi j) (k8m1AYCos i j) < 4) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k8m1AY, k8m1AYCos, k8m1CoreLo, k8m1CoreHi, k8m1TouchLo, k8m1TouchHi, pairExpr, sinNineUpper]

theorem k8m1_AY_angle_lower (x y : Plane) (g : ℝ) (i : Fin 12) (j : Fin 12)
    (hiLo : (k8m1CoreLo i : ℝ) ≤ ‖x‖) (hiHi : ‖x‖ ≤ k8m1CoreHi i)
    (hjLo : (k8m1TouchLo j : ℝ) ≤ ‖y‖) (hjHi : ‖y‖ ≤ k8m1TouchHi j)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (k8m1AY i j : ℝ) / 10000 ≤ g := by
  rcases k8m1_AY_data i j with hz | himp | ⟨hri, hrj, hk0, hkπ, hc, hll, hlh, hhl, hhh⟩
  · simpa [hz] using hg
  · have hn := norm_sub_le x y
    rw [← dist_eq_norm] at hn
    linarith
  · have hkπ' : (k8m1AY i j : ℝ) / 10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
    have hcosLower : (k8m1AYCos i j : ℝ) < Real.cos ((k8m1AY i j : ℝ) / 10000) := by
      apply cos_full_radians_lower_of_certificate _ _ hk0 hkπ'
      convert hc using 1 <;> congr 2 <;> ring
    exact (directed_pair_box_full_radian_gt x y g ((k8m1AY i j : ℝ) / 10000)
      (k8m1AYCos i j) (k8m1CoreLo i) (k8m1CoreHi i) (k8m1TouchLo j) (k8m1TouchHi j)
      hri hrj hiLo hiHi hjLo hjHi hsep hcos hg hk0 hkπ' hcosLower hll hlh hhl hhh).le

theorem k8m1_core_bin_cover (r : ℝ) (hlo : (1 / 8 : ℝ) ≤ r)
    (hhi : r ≤ 131 / 100) :
    ∃ i : Fin 12, (k8m1CoreLo i : ℝ) ≤ r ∧ r ≤ k8m1CoreHi i := by
  by_cases h0 : r ≤ (1 / 4 : ℝ)
  · refine ⟨0, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
  ·
    by_cases h1 : r ≤ (7 / 20 : ℝ)
    · refine ⟨1, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
    ·
      by_cases h2 : r ≤ (9 / 20 : ℝ)
      · refine ⟨2, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
      ·
        by_cases h3 : r ≤ (11 / 20 : ℝ)
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
        ·
          by_cases h4 : r ≤ (13 / 20 : ℝ)
          · refine ⟨4, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
          ·
            by_cases h5 : r ≤ (3 / 4 : ℝ)
            · refine ⟨5, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
            ·
              by_cases h6 : r ≤ (17 / 20 : ℝ)
              · refine ⟨6, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
              ·
                by_cases h7 : r ≤ (19 / 20 : ℝ)
                · refine ⟨7, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
                ·
                  by_cases h8 : r ≤ (21 / 20 : ℝ)
                  · refine ⟨8, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
                  ·
                    by_cases h9 : r ≤ (23 / 20 : ℝ)
                    · refine ⟨9, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
                    ·
                      by_cases h10 : r ≤ (5 / 4 : ℝ)
                      · refine ⟨10, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith
                      ·
                        refine ⟨11, ?_, ?_⟩ <;> norm_num [k8m1CoreLo, k8m1CoreHi] <;> linarith

theorem k8m1_touch_bin_cover (r : ℝ) (hlo : (123 / 100 : ℝ) ≤ r)
    (hhi : r ≤ 4771 / 2000) :
    ∃ i : Fin 12, (k8m1TouchLo i : ℝ) ≤ r ∧ r ≤ k8m1TouchHi i := by
  by_cases h0 : r ≤ (3 / 2 : ℝ)
  · refine ⟨0, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
  ·
    by_cases h1 : r ≤ (8 / 5 : ℝ)
    · refine ⟨1, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
    ·
      by_cases h2 : r ≤ (41 / 25 : ℝ)
      · refine ⟨2, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
      ·
        by_cases h3 : r ≤ (33 / 20 : ℝ)
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
        ·
          by_cases h4 : r ≤ (17 / 10 : ℝ)
          · refine ⟨4, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
          ·
            by_cases h5 : r ≤ (9 / 5 : ℝ)
            · refine ⟨5, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
            ·
              by_cases h6 : r ≤ (19 / 10 : ℝ)
              · refine ⟨6, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
              ·
                by_cases h7 : r ≤ (2 : ℝ)
                · refine ⟨7, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
                ·
                  by_cases h8 : r ≤ (21 / 10 : ℝ)
                  · refine ⟨8, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
                  ·
                    by_cases h9 : r ≤ (11 / 5 : ℝ)
                    · refine ⟨9, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
                    ·
                      by_cases h10 : r ≤ (23 / 10 : ℝ)
                      · refine ⟨10, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith
                      ·
                        refine ⟨11, ?_, ?_⟩ <;> norm_num [k8m1TouchLo, k8m1TouchHi] <;> linarith

theorem k8m1_extra_lower {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) (q : Fin 15) (hinner : ‖p q‖ < b)
    (htouch : TouchesOuter p b q) (i : Fin 12) (hlo : (k8m1TouchLo i : ℝ) ≤ ‖p q‖) :
    (k8m1Extra i : ℝ) / 10000 ≤
      max 0 (2 * contactAngle b ‖p q‖ - 57588 / 100000) := by
  have hgamma : (k8m1Gamma i : ℝ) / 10000 ≤ contactAngle b ‖p q‖ := by
    fin_cases i
    ·
      norm_num [k8m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k8m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k8m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k8m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (33 / 20) (2937 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (17 / 10) (212 / 625) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (9 / 5) (509 / 1250) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (19 / 10) (2283 / 5000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (2) (4941 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (21 / 10) (5233 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (11 / 5) (5461 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k8m1Gamma, k8m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (23 / 10) (5639 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
  have hmax := le_max_right (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  have hnonneg := le_max_left (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  fin_cases i <;> norm_num [k8m1Extra, k8m1Gamma] at hgamma ⊢ <;> linarith

end CP15
