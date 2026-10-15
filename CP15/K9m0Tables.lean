import CP15.K9m0WordCertificate
import CP15.RationalRadianAngle
import CP15.SevenTouchingClosed

namespace CP15

set_option maxHeartbeats 0

theorem k9_bin_data (i j : Fin 7) :
    0 < (k9BinLo i : ℝ) ∧ 0 < (k9BinLo j : ℝ) ∧
    0 ≤ (k9PairUnits i j : ℝ) / 10000 ∧ (k9PairUnits i j : ℝ) / 10000 ≤ 2 ∧
    (k9PairCosBound i j : ℝ) < 1 - 2 *
      ((k9PairUnits i j : ℝ) / 20000 - ((k9PairUnits i j : ℝ) / 20000) ^ 3 / 6 +
        ((k9PairUnits i j : ℝ) / 20000) ^ 5 / 120) ^ 2 ∧
    pairExpr (k9BinLo i) (k9BinLo j) (k9PairCosBound i j) < 4 ∧
    pairExpr (k9BinLo i) (k9BinHi j) (k9PairCosBound i j) < 4 ∧
    pairExpr (k9BinHi i) (k9BinLo j) (k9PairCosBound i j) < 4 ∧
    pairExpr (k9BinHi i) (k9BinHi j) (k9PairCosBound i j) < 4 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k9BinLo, k9BinHi, k9PairUnits, k9PairCosBound, pairExpr]

theorem k9_bin_cover (r : ℝ) (hlo : (123 / 100 : ℝ) ≤ r) (hhi : r ≤ 4771 / 2000) :
    ∃ i : Fin 7, (k9BinLo i : ℝ) ≤ r ∧ r ≤ k9BinHi i := by
  by_cases h0 : r ≤ (3 / 2 : ℝ)
  · refine ⟨0, ?_, ?_⟩ <;> norm_num [k9BinLo, k9BinHi] <;> linarith
  ·
    by_cases h1 : r ≤ (33 / 20 : ℝ)
    · refine ⟨1, ?_, ?_⟩ <;> norm_num [k9BinLo, k9BinHi] <;> linarith
    ·
      by_cases h2 : r ≤ (9 / 5 : ℝ)
      · refine ⟨2, ?_, ?_⟩ <;> norm_num [k9BinLo, k9BinHi] <;> linarith
      ·
        by_cases h3 : r ≤ (39 / 20 : ℝ)
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [k9BinLo, k9BinHi] <;> linarith
        ·
          by_cases h4 : r ≤ (21 / 10 : ℝ)
          · refine ⟨4, ?_, ?_⟩ <;> norm_num [k9BinLo, k9BinHi] <;> linarith
          ·
            by_cases h5 : r ≤ (9 / 4 : ℝ)
            · refine ⟨5, ?_, ?_⟩ <;> norm_num [k9BinLo, k9BinHi] <;> linarith
            ·
              refine ⟨6, ?_, ?_⟩ <;> norm_num [k9BinLo, k9BinHi] <;> linarith

theorem k9_bin_pair_angle_lower (x y : Plane) (g : ℝ) (i j : Fin 7)
    (hiLo : (k9BinLo i : ℝ) ≤ ‖x‖) (hiHi : ‖x‖ ≤ k9BinHi i)
    (hjLo : (k9BinLo j : ℝ) ≤ ‖y‖) (hjHi : ‖y‖ ≤ k9BinHi j)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) (hg : 0 ≤ g) :
    (k9PairUnits i j : ℝ) / 10000 ≤ g := by
  rcases k9_bin_data i j with ⟨hri, hrj, hk0, hk2, hc, hll, hlh, hhl, hhh⟩
  have hcosLower : (k9PairCosBound i j : ℝ) < Real.cos ((k9PairUnits i j : ℝ) / 10000) := by
    apply cos_radians_lower_of_certificate _ _ hk0 hk2
    convert hc using 1 <;> ring
  exact (directed_pair_box_radian_gt x y g ((k9PairUnits i j : ℝ) / 10000)
    (k9PairCosBound i j) (k9BinLo i) (k9BinHi i) (k9BinLo j) (k9BinHi j)
    hri hrj hiLo hiHi hjLo hjHi hsep hcos hg hk0 hk2 hcosLower hll hlh hhl hhh).le

theorem k9_bin_extra_lower {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (q : Fin 15) (hinner : ‖p q‖ < b) (htouch : TouchesOuter p b q)
    (i : Fin 7) (hlo : (k9BinLo i : ℝ) ≤ ‖p q‖) :
    (k9ExtraUnits i : ℝ) / 10000 ≤
      max 0 (2 * contactAngle b ‖p q‖ - 57588 / 100000) := by
  have hb : 3 < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5, h.elementaryLower]
  have hbB : b ≤ (17607 / 5000 : ℝ) :=
    (h.belowCandidate.trans_lt Candidate.candidateB_lt_352136_div_100000).le.trans (by norm_num)
  have hrHi : ‖p q‖ ≤ 12 / 5 :=
    ((h.innerCap q hinner).trans (D_lt_twelve_fifths_of_le_candidateB b (by linarith) h.belowCandidate)).le
  have hgamma : (k9GammaUnits i : ℝ) / 10000 ≤ contactAngle b ‖p q‖ := by
    fin_cases i
    ·
      norm_num [k9GammaUnits]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9GammaUnits]
      exact Real.arccos_nonneg _
    ·
      norm_num [k9BinLo, k9GammaUnits] at hlo ⊢
      obtain ⟨z, _, hz, hc⟩ := htouch
      have hlaw := actual_contactAngle_cosine_law (p q) (p z) b (by linarith) (by linarith) hz hc
      exact (contact_offset_gt_rational_angle b (17607 / 5000) (33 / 20) ‖p q‖
        (contactAngle b ‖p q‖) (2937 / 10000) hb hbB (by norm_num) (by norm_num) hlo hrHi
        (Real.arccos_nonneg _) (Real.arccos_le_pi _) (by norm_num) (by norm_num)
        (by norm_num [contactCos, sinCubicUpper]) hlaw).le
    ·
      norm_num [k9BinLo, k9GammaUnits] at hlo ⊢
      obtain ⟨z, _, hz, hc⟩ := htouch
      have hlaw := actual_contactAngle_cosine_law (p q) (p z) b (by linarith) (by linarith) hz hc
      exact (contact_offset_gt_rational_angle b (17607 / 5000) (9 / 5) ‖p q‖
        (contactAngle b ‖p q‖) (509 / 1250) hb hbB (by norm_num) (by norm_num) hlo hrHi
        (Real.arccos_nonneg _) (Real.arccos_le_pi _) (by norm_num) (by norm_num)
        (by norm_num [contactCos, sinCubicUpper]) hlaw).le
    ·
      norm_num [k9BinLo, k9GammaUnits] at hlo ⊢
      obtain ⟨z, _, hz, hc⟩ := htouch
      have hlaw := actual_contactAngle_cosine_law (p q) (p z) b (by linarith) (by linarith) hz hc
      exact (contact_offset_gt_rational_angle b (17607 / 5000) (39 / 20) ‖p q‖
        (contactAngle b ‖p q‖) (2383 / 5000) hb hbB (by norm_num) (by norm_num) hlo hrHi
        (Real.arccos_nonneg _) (Real.arccos_le_pi _) (by norm_num) (by norm_num)
        (by norm_num [contactCos, sinCubicUpper]) hlaw).le
    ·
      norm_num [k9BinLo, k9GammaUnits] at hlo ⊢
      obtain ⟨z, _, hz, hc⟩ := htouch
      have hlaw := actual_contactAngle_cosine_law (p q) (p z) b (by linarith) (by linarith) hz hc
      exact (contact_offset_gt_rational_angle b (17607 / 5000) (21 / 10) ‖p q‖
        (contactAngle b ‖p q‖) (5233 / 10000) hb hbB (by norm_num) (by norm_num) hlo hrHi
        (Real.arccos_nonneg _) (Real.arccos_le_pi _) (by norm_num) (by norm_num)
        (by norm_num [contactCos, sinCubicUpper]) hlaw).le
    ·
      norm_num [k9BinLo, k9GammaUnits] at hlo ⊢
      obtain ⟨z, _, hz, hc⟩ := htouch
      have hlaw := actual_contactAngle_cosine_law (p q) (p z) b (by linarith) (by linarith) hz hc
      exact (contact_offset_gt_rational_angle b (17607 / 5000) (9 / 4) ‖p q‖
        (contactAngle b ‖p q‖) (1111 / 2000) hb hbB (by norm_num) (by norm_num) hlo hrHi
        (Real.arccos_nonneg _) (Real.arccos_le_pi _) (by norm_num) (by norm_num)
        (by norm_num [contactCos, sinCubicUpper]) hlaw).le
  have hmax := le_max_right (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  have hnonneg := le_max_left (0 : ℝ) (2 * contactAngle b ‖p q‖ - 57588 / 100000)
  fin_cases i <;> norm_num [k9ExtraUnits, k9GammaUnits] at hgamma ⊢ <;> linarith

end CP15
