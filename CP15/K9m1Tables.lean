import CP15.K9m1DiscreteData
import CP15.RationalFullAngle
import CP15.OneCoreBounds

namespace CP15

set_option maxHeartbeats 0

theorem k9m1_YY_data (i : Fin 20) (j : Fin 20) :
    k9m1YY i j = 0 ∨ (k9m1TouchHi i : ℝ) + k9m1TouchHi j < 2 ∨
      (0 < (k9m1TouchLo i : ℝ) ∧ 0 < (k9m1TouchLo j : ℝ) ∧
        0 ≤ (k9m1YY i j : ℝ) / 10000 ∧ (k9m1YY i j : ℝ) / 10000 ≤ 31415 / 10000 ∧
        (k9m1YYCos i j : ℝ) < 1 - 2 * sinNineUpper ((k9m1YY i j : ℝ) / 20000) ^ 2 ∧
        pairExpr (k9m1TouchLo i) (k9m1TouchLo j) (k9m1YYCos i j) < 4 ∧
        pairExpr (k9m1TouchLo i) (k9m1TouchHi j) (k9m1YYCos i j) < 4 ∧
        pairExpr (k9m1TouchHi i) (k9m1TouchLo j) (k9m1YYCos i j) < 4 ∧
        pairExpr (k9m1TouchHi i) (k9m1TouchHi j) (k9m1YYCos i j) < 4) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k9m1YY, k9m1YYCos, k9m1TouchLo, k9m1TouchHi, k9m1TouchLo, k9m1TouchHi, pairExpr, sinNineUpper]

theorem k9m1_YY_angle_lower (x y : Plane) (g : ℝ) (i : Fin 20) (j : Fin 20)
    (hiLo : (k9m1TouchLo i : ℝ) ≤ ‖x‖) (hiHi : ‖x‖ ≤ k9m1TouchHi i)
    (hjLo : (k9m1TouchLo j : ℝ) ≤ ‖y‖) (hjHi : ‖y‖ ≤ k9m1TouchHi j)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (k9m1YY i j : ℝ) / 10000 ≤ g := by
  rcases k9m1_YY_data i j with hz | himp | ⟨hri, hrj, hk0, hkπ, hc, hll, hlh, hhl, hhh⟩
  · simpa [hz] using hg
  · have hn := norm_sub_le x y
    rw [← dist_eq_norm] at hn
    linarith
  · have hkπ' : (k9m1YY i j : ℝ) / 10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
    have hcosLower : (k9m1YYCos i j : ℝ) < Real.cos ((k9m1YY i j : ℝ) / 10000) := by
      apply cos_full_radians_lower_of_certificate _ _ hk0 hkπ'
      convert hc using 1 <;> congr 2 <;> ring
    exact (directed_pair_box_full_radian_gt x y g ((k9m1YY i j : ℝ) / 10000)
      (k9m1YYCos i j) (k9m1TouchLo i) (k9m1TouchHi i) (k9m1TouchLo j) (k9m1TouchHi j)
      hri hrj hiLo hiHi hjLo hjHi hsep hcos hg hk0 hkπ' hcosLower hll hlh hhl hhh).le

theorem k9m1_AY_data (i : Fin 11) (j : Fin 20) :
    k9m1AY i j = 0 ∨ (k9m1CoreHi i : ℝ) + k9m1TouchHi j < 2 ∨
      (0 < (k9m1CoreLo i : ℝ) ∧ 0 < (k9m1TouchLo j : ℝ) ∧
        0 ≤ (k9m1AY i j : ℝ) / 10000 ∧ (k9m1AY i j : ℝ) / 10000 ≤ 31415 / 10000 ∧
        (k9m1AYCos i j : ℝ) < 1 - 2 * sinNineUpper ((k9m1AY i j : ℝ) / 20000) ^ 2 ∧
        pairExpr (k9m1CoreLo i) (k9m1TouchLo j) (k9m1AYCos i j) < 4 ∧
        pairExpr (k9m1CoreLo i) (k9m1TouchHi j) (k9m1AYCos i j) < 4 ∧
        pairExpr (k9m1CoreHi i) (k9m1TouchLo j) (k9m1AYCos i j) < 4 ∧
        pairExpr (k9m1CoreHi i) (k9m1TouchHi j) (k9m1AYCos i j) < 4) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k9m1AY, k9m1AYCos, k9m1CoreLo, k9m1CoreHi, k9m1TouchLo, k9m1TouchHi, pairExpr, sinNineUpper]

theorem k9m1_AY_angle_lower (x y : Plane) (g : ℝ) (i : Fin 11) (j : Fin 20)
    (hiLo : (k9m1CoreLo i : ℝ) ≤ ‖x‖) (hiHi : ‖x‖ ≤ k9m1CoreHi i)
    (hjLo : (k9m1TouchLo j : ℝ) ≤ ‖y‖) (hjHi : ‖y‖ ≤ k9m1TouchHi j)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (k9m1AY i j : ℝ) / 10000 ≤ g := by
  rcases k9m1_AY_data i j with hz | himp | ⟨hri, hrj, hk0, hkπ, hc, hll, hlh, hhl, hhh⟩
  · simpa [hz] using hg
  · have hn := norm_sub_le x y
    rw [← dist_eq_norm] at hn
    linarith
  · have hkπ' : (k9m1AY i j : ℝ) / 10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
    have hcosLower : (k9m1AYCos i j : ℝ) < Real.cos ((k9m1AY i j : ℝ) / 10000) := by
      apply cos_full_radians_lower_of_certificate _ _ hk0 hkπ'
      convert hc using 1 <;> congr 2 <;> ring
    exact (directed_pair_box_full_radian_gt x y g ((k9m1AY i j : ℝ) / 10000)
      (k9m1AYCos i j) (k9m1CoreLo i) (k9m1CoreHi i) (k9m1TouchLo j) (k9m1TouchHi j)
      hri hrj hiLo hiHi hjLo hjHi hsep hcos hg hk0 hkπ' hcosLower hll hlh hhl hhh).le

theorem k9m1_core_bin_cover (r : ℝ) (hlo : (1 / 5 : ℝ) ≤ r)
    (hhi : r ≤ 131 / 100) :
    ∃ i : Fin 11, (k9m1CoreLo i : ℝ) ≤ r ∧ r ≤ k9m1CoreHi i := by
  by_cases h0 : r ≤ (3 / 10 : ℝ)
  · refine ⟨0, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
  ·
    by_cases h1 : r ≤ (2 / 5 : ℝ)
    · refine ⟨1, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
    ·
      by_cases h2 : r ≤ (1 / 2 : ℝ)
      · refine ⟨2, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
      ·
        by_cases h3 : r ≤ (3 / 5 : ℝ)
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
        ·
          by_cases h4 : r ≤ (7 / 10 : ℝ)
          · refine ⟨4, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
          ·
            by_cases h5 : r ≤ (4 / 5 : ℝ)
            · refine ⟨5, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
            ·
              by_cases h6 : r ≤ (9 / 10 : ℝ)
              · refine ⟨6, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
              ·
                by_cases h7 : r ≤ (1 : ℝ)
                · refine ⟨7, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
                ·
                  by_cases h8 : r ≤ (11 / 10 : ℝ)
                  · refine ⟨8, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
                  ·
                    by_cases h9 : r ≤ (6 / 5 : ℝ)
                    · refine ⟨9, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith
                    ·
                      refine ⟨10, ?_, ?_⟩ <;> norm_num [k9m1CoreLo, k9m1CoreHi] <;> linarith

theorem k9m1_touch_bin_cover (r : ℝ) (hlo : (123 / 100 : ℝ) ≤ r)
    (hhi : r ≤ 4771 / 2000) :
    ∃ i : Fin 20, (k9m1TouchLo i : ℝ) ≤ r ∧ r ≤ k9m1TouchHi i := by
  by_cases h0 : r ≤ (27 / 20 : ℝ)
  · refine ⟨0, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
  ·
    by_cases h1 : r ≤ (29 / 20 : ℝ)
    · refine ⟨1, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
    ·
      by_cases h2 : r ≤ (3 / 2 : ℝ)
      · refine ⟨2, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
      ·
        by_cases h3 : r ≤ (31 / 20 : ℝ)
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
        ·
          by_cases h4 : r ≤ (8 / 5 : ℝ)
          · refine ⟨4, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
          ·
            by_cases h5 : r ≤ (41 / 25 : ℝ)
            · refine ⟨5, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
            ·
              by_cases h6 : r ≤ (33 / 20 : ℝ)
              · refine ⟨6, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
              ·
                by_cases h7 : r ≤ (17 / 10 : ℝ)
                · refine ⟨7, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                ·
                  by_cases h8 : r ≤ (7 / 4 : ℝ)
                  · refine ⟨8, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                  ·
                    by_cases h9 : r ≤ (9 / 5 : ℝ)
                    · refine ⟨9, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                    ·
                      by_cases h10 : r ≤ (19 / 10 : ℝ)
                      · refine ⟨10, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                      ·
                        by_cases h11 : r ≤ (2 : ℝ)
                        · refine ⟨11, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                        ·
                          by_cases h12 : r ≤ (41 / 20 : ℝ)
                          · refine ⟨12, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                          ·
                            by_cases h13 : r ≤ (21 / 10 : ℝ)
                            · refine ⟨13, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                            ·
                              by_cases h14 : r ≤ (43 / 20 : ℝ)
                              · refine ⟨14, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                              ·
                                by_cases h15 : r ≤ (11 / 5 : ℝ)
                                · refine ⟨15, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                                ·
                                  by_cases h16 : r ≤ (9 / 4 : ℝ)
                                  · refine ⟨16, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                                  ·
                                    by_cases h17 : r ≤ (23 / 10 : ℝ)
                                    · refine ⟨17, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                                    ·
                                      by_cases h18 : r ≤ (47 / 20 : ℝ)
                                      · refine ⟨18, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith
                                      ·
                                        refine ⟨19, ?_, ?_⟩ <;> norm_num [k9m1TouchLo, k9m1TouchHi] <;> linarith

theorem k9m1_extra_lower {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) (q : Fin 15) (hinner : ‖p q‖ < b)
    (htouch : TouchesOuter p b q) (i : Fin 20) (hlo : (k9m1TouchLo i : ℝ) ≤ ‖p q‖) :
    (k9m1Extra i : ℝ) / 10000 ≤
      max 0 (2 * contactAngle b ‖p q‖ - 57588 / 100000) := by
  have hgamma : (k9m1Gamma i : ℝ) / 10000 ≤ contactAngle b ‖p q‖ := by
    fin_cases i
    ·
      norm_num [k9m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9m1Gamma]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (33 / 20) (2937 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (17 / 10) (212 / 625) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (7 / 4) (1881 / 5000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (9 / 5) (509 / 1250) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (19 / 10) (2283 / 5000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (2) (4941 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (41 / 20) (637 / 1250) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (21 / 10) (5233 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (43 / 20) (2677 / 5000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (11 / 5) (5461 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (9 / 4) (1111 / 2000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (23 / 10) (5639 / 10000) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
    ·
      norm_num [k9m1Gamma, k9m1TouchLo] at hlo ⊢
      exact (h.touching_angle_gt_of_rational_corner q hinner htouch
        (47 / 20) (357 / 625) (by norm_num) hlo
        (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])).le
  have hmax := le_max_right (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  have hnonneg := le_max_left (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  fin_cases i <;> norm_num [k9m1Extra, k9m1Gamma] at hgamma ⊢ <;> linarith

end CP15
