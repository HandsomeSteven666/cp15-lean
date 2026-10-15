import CP15.DistinctSupportCertificate

namespace CP15

set_option maxHeartbeats 0

/-- A complete twelve-leaf closed rational cover of an enlarged core-radius
rectangle. Nine leaves use four actual directed clearance angles; three
use the minimum possible strict-blocker support. Every number and every
branch is checked by Lean, independently of the certificate producer. -/
theorem distinct_case_ii_scalar_cover (a z y q l t : Plane)
    (b d e gAA gZH gHL gAL : ℝ)
    (hb : 3 < b) (hbB : b ≤ (352136 / 100000 : ℝ))
    (haLo : (699 / 1000 : ℝ) ≤ ‖a‖) (haHi : ‖a‖ ≤ 1301 / 1000)
    (hzLo : (699 / 1000 : ℝ) ≤ ‖z‖) (hzHi : ‖z‖ ≤ 1301 / 1000)
    (hyLo : (2 : ℝ) ≤ ‖y‖) (hyHi : ‖y‖ ≤ 2385436 / 1000000)
    (hqLo : (2 : ℝ) ≤ ‖q‖) (hqHi : ‖q‖ ≤ 2385436 / 1000000)
    (hlLo : (3 / 2 : ℝ) ≤ ‖l‖) (hlHi : ‖l‖ ≤ 2)
    (htLo : (3 / 2 : ℝ) ≤ ‖t‖) (htHi : ‖t‖ ≤ 2)
    (hysq : 4 + ‖a‖ ^ 2 < ‖y‖ ^ 2) (hqsq : 4 + ‖z‖ ^ 2 < ‖q‖ ^ 2)
    (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi) (he0 : 0 ≤ e) (hepi : e ≤ Real.pi)
    (hdlaw : 2 * ‖y‖ * b * Real.cos d = b ^ 2 + ‖y‖ ^ 2 - 4)
    (helaw : 2 * ‖q‖ * b * Real.cos e = b ^ 2 + ‖q‖ ^ 2 - 4)
    (hbudget : 2 * d + 2 * e + 7 * (57588 / 100000 : ℝ) ≤ 2 * Real.pi)
    (hsepAA : 2 ≤ dist a z) (hsepZH : 2 ≤ dist z q)
    (hsepHL : 2 ≤ dist q l) (hsepAL : 2 ≤ dist a t)
    (hcosAA : Real.cos (polarArg a - polarArg z) = Real.cos gAA)
    (hcosZH : Real.cos (polarArg z - polarArg q) = Real.cos gZH)
    (hcosHL : Real.cos (polarArg q - polarArg l) = Real.cos gHL)
    (hcosAL : Real.cos (polarArg a - polarArg t) = Real.cos gAL)
    (hgAA : 0 ≤ gAA) (hgZH : 0 ≤ gZH) (hgHL : 0 ≤ gHL) (hgAL : 0 ≤ gAL)
    (hangleBudget : gAA + gZH + gHL + gAL ≤ 300 * Real.pi / 180) : False := by
  by_cases hcell0 : ‖a‖ ≤ (1 : ℝ)
  ·
    by_cases hcell1 : ‖z‖ ≤ (1 : ℝ)
    ·
      have hcap : ‖q‖ ≤ (596359 / 250000 : ℝ) := by linarith
      have hangle0 : (179991 / 1000 : ℝ) * Real.pi / 180 < gAA := by
        apply directed_pair_box_angle_gt_full a z gAA (179991 / 1000 : ℝ) (-99999999 / 100000000 : ℝ)
          (699 / 1000 : ℝ) (1 : ℝ) (699 / 1000 : ℝ) (1 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepAA hcosAA hgAA (by norm_num) (by norm_num)
        · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          · norm_num
          · norm_num
        all_goals norm_num [pairExpr]
      have hangle1 : (246 / 5 : ℝ) * Real.pi / 180 < gZH := by
        apply directed_pair_box_angle_gt_full z q gZH (246 / 5 : ℝ) (32668827 / 50000000 : ℝ)
          (699 / 1000 : ℝ) (1 : ℝ) (2 : ℝ) (596359 / 250000 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepZH hcosZH hgZH (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      have hangle2 : (10677 / 200 : ℝ) * Real.pi / 180 < gHL := by
        apply directed_pair_box_angle_gt_full q l gHL (10677 / 200 : ℝ) (59635901 / 100000000 : ℝ)
          (2 : ℝ) (596359 / 250000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepHL hcosHL hgHL (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      have hangle3 : (7549 / 100 : ℝ) * Real.pi / 180 < gAL := by
        apply directed_pair_box_angle_gt_full a t gAL (7549 / 100 : ℝ) (25000001 / 100000000 : ℝ)
          (699 / 1000 : ℝ) (1 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepAL hcosAL hgAL (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      nlinarith [Real.pi_pos]
    ·
      have hcap : ‖q‖ ≤ (596359 / 250000 : ℝ) := by linarith
      have hangle0 : (60081 / 500 : ℝ) * Real.pi / 180 < gAA := by
        apply directed_pair_box_angle_gt_full a z gAA (60081 / 500 : ℝ) (-25122963 / 50000000 : ℝ)
          (699 / 1000 : ℝ) (1 : ℝ) (1 : ℝ) (1301 / 1000 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepAA hcosAA hgAA (by norm_num) (by norm_num)
        · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          · norm_num
          · norm_num
        all_goals norm_num [pairExpr]
      have hangle1 : (55667 / 1000 : ℝ) * Real.pi / 180 < gZH := by
        apply directed_pair_box_angle_gt_full z q gZH (55667 / 1000 : ℝ) (28195107 / 50000000 : ℝ)
          (1 : ℝ) (1301 / 1000 : ℝ) (2 : ℝ) (596359 / 250000 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepZH hcosZH hgZH (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      have hangle2 : (10677 / 200 : ℝ) * Real.pi / 180 < gHL := by
        apply directed_pair_box_angle_gt_full q l gHL (10677 / 200 : ℝ) (59635901 / 100000000 : ℝ)
          (2 : ℝ) (596359 / 250000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepHL hcosHL hgHL (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      have hangle3 : (7549 / 100 : ℝ) * Real.pi / 180 < gAL := by
        apply directed_pair_box_angle_gt_full a t gAL (7549 / 100 : ℝ) (25000001 / 100000000 : ℝ)
          (699 / 1000 : ℝ) (1 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
          (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by linarith) (by linarith)
          hsepAL hcosAL hgAL (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      nlinarith [Real.pi_pos]
  ·
    by_cases hcell2 : ‖z‖ ≤ (1 : ℝ)
    ·
      by_cases hcell3 : ‖a‖ ≤ (2301 / 2000 : ℝ)
      ·
        have hroot1 : (2236067 / 1000000 : ℝ) ≤ ‖y‖ := by
          apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (1 : ℝ) (2236067 / 1000000 : ℝ)
            (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
          norm_num
        have hcap : ‖q‖ ≤ (295293 / 125000 : ℝ) := by
          by_contra hcapNo
          exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
            (2236067 / 1000000 : ℝ) (295293 / 125000 : ℝ) (276547 / 500000 : ℝ) (14323 / 25000 : ℝ)
            hb (by linarith) (by norm_num) (by norm_num)
            hroot1 (by linarith) (by linarith) (by linarith)
            hd0 hdpi he0 hepi hdlaw helaw
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num [contactCos, sinCubicUpper])
            (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
        have hangle0 : (136763 / 1000 : ℝ) * Real.pi / 180 < gAA := by
          apply directed_pair_box_angle_gt_full a z gAA (136763 / 1000 : ℝ) (-9106637 / 12500000 : ℝ)
            (1 : ℝ) (2301 / 2000 : ℝ) (699 / 1000 : ℝ) (1 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepAA hcosAA hgAA (by norm_num) (by norm_num)
          · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            · norm_num
            · norm_num
          all_goals norm_num [pairExpr]
        have hangle1 : (25599 / 500 : ℝ) * Real.pi / 180 < gZH := by
          apply directed_pair_box_angle_gt_full z q gZH (25599 / 500 : ℝ) (6265661 / 10000000 : ℝ)
            (699 / 1000 : ℝ) (1 : ℝ) (2 : ℝ) (295293 / 125000 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepZH hcosZH hgZH (by norm_num) (by norm_num)
          · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            norm_num
          all_goals norm_num [pairExpr]
        have hangle2 : (13449 / 250 : ℝ) * Real.pi / 180 < gHL := by
          apply directed_pair_box_angle_gt_full q l gHL (13449 / 250 : ℝ) (59058601 / 100000000 : ℝ)
            (2 : ℝ) (295293 / 125000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepHL hcosHL hgHL (by norm_num) (by norm_num)
          · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            norm_num
          all_goals norm_num [pairExpr]
        have hangle3 : (73257 / 1000 : ℝ) * Real.pi / 180 < gAL := by
          apply directed_pair_box_angle_gt_full a t gAL (73257 / 1000 : ℝ) (28762501 / 100000000 : ℝ)
            (1 : ℝ) (2301 / 2000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepAL hcosAL hgAL (by norm_num) (by norm_num)
          · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            norm_num
          all_goals norm_num [pairExpr]
        nlinarith [Real.pi_pos]
      ·
        have hroot1 : (2307303 / 1000000 : ℝ) ≤ ‖y‖ := by
          apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (2301 / 2000 : ℝ) (2307303 / 1000000 : ℝ)
            (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
          norm_num
        have hcap : ‖q‖ ≤ (2281257 / 1000000 : ℝ) := by
          by_contra hcapNo
          exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
            (2307303 / 1000000 : ℝ) (2281257 / 1000000 : ℝ) (565071 / 1000000 : ℝ) (560943 / 1000000 : ℝ)
            hb (by linarith) (by norm_num) (by norm_num)
            hroot1 (by linarith) (by linarith) (by linarith)
            hd0 hdpi he0 hepi hdlaw helaw
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num [contactCos, sinCubicUpper])
            (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
        have hangle0 : (60081 / 500 : ℝ) * Real.pi / 180 < gAA := by
          apply directed_pair_box_angle_gt_full a z gAA (60081 / 500 : ℝ) (-25122963 / 50000000 : ℝ)
            (2301 / 2000 : ℝ) (1301 / 1000 : ℝ) (699 / 1000 : ℝ) (1 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepAA hcosAA hgAA (by norm_num) (by norm_num)
          · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            · norm_num
            · norm_num
          all_goals norm_num [pairExpr]
        have hangle1 : (28967 / 500 : ℝ) * Real.pi / 180 < gZH := by
          apply directed_pair_box_angle_gt_full z q gZH (28967 / 500 : ℝ) (26538567 / 50000000 : ℝ)
            (699 / 1000 : ℝ) (1 : ℝ) (2 : ℝ) (2281257 / 1000000 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepZH hcosZH hgZH (by norm_num) (by norm_num)
          · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            norm_num
          all_goals norm_num [pairExpr]
        have hangle2 : (27611 / 500 : ℝ) * Real.pi / 180 < gHL := by
          apply directed_pair_box_angle_gt_full q l gHL (27611 / 500 : ℝ) (28515713 / 50000000 : ℝ)
            (2 : ℝ) (2281257 / 1000000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepHL hcosHL hgHL (by norm_num) (by norm_num)
          · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            norm_num
          all_goals norm_num [pairExpr]
        have hangle3 : (17749 / 250 : ℝ) * Real.pi / 180 < gAL := by
          apply directed_pair_box_angle_gt_full a t gAL (17749 / 250 : ℝ) (32525001 / 100000000 : ℝ)
            (2301 / 2000 : ℝ) (1301 / 1000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
            (by norm_num) (by norm_num) (by linarith) (by linarith)
            (by linarith) (by linarith)
            hsepAL hcosAL hgAL (by norm_num) (by norm_num)
          · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
            norm_num
          all_goals norm_num [pairExpr]
        nlinarith [Real.pi_pos]
    ·
      by_cases hcell4 : ‖a‖ ≤ (2301 / 2000 : ℝ)
      ·
        by_cases hcell5 : ‖z‖ ≤ (2301 / 2000 : ℝ)
        ·
          have hroot1 : (2236067 / 1000000 : ℝ) ≤ ‖y‖ := by
            apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (1 : ℝ) (2236067 / 1000000 : ℝ)
              (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
            norm_num
          have hcap : ‖q‖ ≤ (295293 / 125000 : ℝ) := by
            by_contra hcapNo
            exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
              (2236067 / 1000000 : ℝ) (295293 / 125000 : ℝ) (276547 / 500000 : ℝ) (14323 / 25000 : ℝ)
              hb (by linarith) (by norm_num) (by norm_num)
              hroot1 (by linarith) (by linarith) (by linarith)
              hd0 hdpi he0 hepi hdlaw helaw
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num [contactCos, sinCubicUpper])
              (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
          have hangle0 : (15091 / 125 : ℝ) * Real.pi / 180 < gAA := by
            apply directed_pair_box_angle_gt_full a z gAA (15091 / 125 : ℝ) (-10219463 / 20000000 : ℝ)
              (1 : ℝ) (2301 / 2000 : ℝ) (1 : ℝ) (2301 / 2000 : ℝ)
              (by norm_num) (by norm_num) (by linarith) (by linarith)
              (by linarith) (by linarith)
              hsepAA hcosAA hgAA (by norm_num) (by norm_num)
            · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
              · norm_num
              · norm_num
            all_goals norm_num [pairExpr]
          have hangle1 : (11377 / 200 : ℝ) * Real.pi / 180 < gZH := by
            apply directed_pair_box_angle_gt_full z q gZH (11377 / 200 : ℝ) (3413809 / 6250000 : ℝ)
              (1 : ℝ) (2301 / 2000 : ℝ) (2 : ℝ) (295293 / 125000 : ℝ)
              (by norm_num) (by norm_num) (by linarith) (by linarith)
              (by linarith) (by linarith)
              hsepZH hcosZH hgZH (by norm_num) (by norm_num)
            · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
              norm_num
            all_goals norm_num [pairExpr]
          have hangle2 : (13449 / 250 : ℝ) * Real.pi / 180 < gHL := by
            apply directed_pair_box_angle_gt_full q l gHL (13449 / 250 : ℝ) (59058601 / 100000000 : ℝ)
              (2 : ℝ) (295293 / 125000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
              (by norm_num) (by norm_num) (by linarith) (by linarith)
              (by linarith) (by linarith)
              hsepHL hcosHL hgHL (by norm_num) (by norm_num)
            · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
              norm_num
            all_goals norm_num [pairExpr]
          have hangle3 : (73257 / 1000 : ℝ) * Real.pi / 180 < gAL := by
            apply directed_pair_box_angle_gt_full a t gAL (73257 / 1000 : ℝ) (28762501 / 100000000 : ℝ)
              (1 : ℝ) (2301 / 2000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
              (by norm_num) (by norm_num) (by linarith) (by linarith)
              (by linarith) (by linarith)
              hsepAL hcosAL hgAL (by norm_num) (by norm_num)
            · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
              norm_num
            all_goals norm_num [pairExpr]
          nlinarith [Real.pi_pos]
        ·
          by_cases hcell6 : ‖a‖ ≤ (4301 / 4000 : ℝ)
          ·
            have hroot1 : (2236067 / 1000000 : ℝ) ≤ ‖y‖ := by
              apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (1 : ℝ) (2236067 / 1000000 : ℝ)
                (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
              norm_num
            have hcap : ‖q‖ ≤ (295293 / 125000 : ℝ) := by
              by_contra hcapNo
              exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
                (2236067 / 1000000 : ℝ) (295293 / 125000 : ℝ) (276547 / 500000 : ℝ) (14323 / 25000 : ℝ)
                hb (by linarith) (by norm_num) (by norm_num)
                hroot1 (by linarith) (by linarith) (by linarith)
                hd0 hdpi he0 hepi hdlaw helaw
                (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (by norm_num [contactCos, sinCubicUpper])
                (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
            have hangle0 : (114297 / 1000 : ℝ) * Real.pi / 180 < gAA := by
              apply directed_pair_box_angle_gt_full a z gAA (114297 / 1000 : ℝ) (-4114791 / 10000000 : ℝ)
                (1 : ℝ) (4301 / 4000 : ℝ) (2301 / 2000 : ℝ) (1301 / 1000 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepAA hcosAA hgAA (by norm_num) (by norm_num)
              · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                · norm_num
                · norm_num
              all_goals norm_num [pairExpr]
            have hangle1 : (7212 / 125 : ℝ) * Real.pi / 180 < gZH := by
              apply directed_pair_box_angle_gt_full z q gZH (7212 / 125 : ℝ) (53429933 / 100000000 : ℝ)
                (2301 / 2000 : ℝ) (1301 / 1000 : ℝ) (2 : ℝ) (295293 / 125000 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepZH hcosZH hgZH (by norm_num) (by norm_num)
              · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                norm_num
              all_goals norm_num [pairExpr]
            have hangle2 : (13449 / 250 : ℝ) * Real.pi / 180 < gHL := by
              apply directed_pair_box_angle_gt_full q l gHL (13449 / 250 : ℝ) (59058601 / 100000000 : ℝ)
                (2 : ℝ) (295293 / 125000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepHL hcosHL hgHL (by norm_num) (by norm_num)
              · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                norm_num
              all_goals norm_num [pairExpr]
            have hangle3 : (74377 / 1000 : ℝ) * Real.pi / 180 < gAL := by
              apply directed_pair_box_angle_gt_full a t gAL (74377 / 1000 : ℝ) (26881251 / 100000000 : ℝ)
                (1 : ℝ) (4301 / 4000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepAL hcosAL hgAL (by norm_num) (by norm_num)
              · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                norm_num
              all_goals norm_num [pairExpr]
            nlinarith [Real.pi_pos]
          ·
            by_cases hcell7 : ‖z‖ ≤ (4903 / 4000 : ℝ)
            ·
              have hroot1 : (1135359 / 500000 : ℝ) ≤ ‖y‖ := by
                apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (4301 / 4000 : ℝ) (1135359 / 500000 : ℝ)
                  (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
                norm_num
              have hcap : ‖q‖ ≤ (2318901 / 1000000 : ℝ) := by
                by_contra hcapNo
                exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
                  (1135359 / 500000 : ℝ) (2318901 / 1000000 : ℝ) (69899 / 125000 : ℝ) (283411 / 500000 : ℝ)
                  hb (by linarith) (by norm_num) (by norm_num)
                  hroot1 (by linarith) (by linarith) (by linarith)
                  hd0 hdpi he0 hepi hdlaw helaw
                  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  (by norm_num [contactCos, sinCubicUpper])
                  (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
              have hangle0 : (22919 / 200 : ℝ) * Real.pi / 180 < gAA := by
                apply directed_pair_box_angle_gt_full a z gAA (22919 / 200 : ℝ) (-20810267 / 50000000 : ℝ)
                  (4301 / 4000 : ℝ) (2301 / 2000 : ℝ) (2301 / 2000 : ℝ) (4903 / 4000 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepAA hcosAA hgAA (by norm_num) (by norm_num)
                · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  · norm_num
                  · norm_num
                all_goals norm_num [pairExpr]
              have hangle1 : (11911 / 200 : ℝ) * Real.pi / 180 < gZH := by
                apply directed_pair_box_angle_gt_full z q gZH (11911 / 200 : ℝ) (10131481 / 20000000 : ℝ)
                  (2301 / 2000 : ℝ) (4903 / 4000 : ℝ) (2 : ℝ) (2318901 / 1000000 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepZH hcosZH hgZH (by norm_num) (by norm_num)
                · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  norm_num
                all_goals norm_num [pairExpr]
              have hangle2 : (54563 / 1000 : ℝ) * Real.pi / 180 < gHL := by
                apply directed_pair_box_angle_gt_full q l gHL (54563 / 1000 : ℝ) (28986263 / 50000000 : ℝ)
                  (2 : ℝ) (2318901 / 1000000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepHL hcosHL hgHL (by norm_num) (by norm_num)
                · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  norm_num
                all_goals norm_num [pairExpr]
              have hangle3 : (73257 / 1000 : ℝ) * Real.pi / 180 < gAL := by
                apply directed_pair_box_angle_gt_full a t gAL (73257 / 1000 : ℝ) (28762501 / 100000000 : ℝ)
                  (4301 / 4000 : ℝ) (2301 / 2000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepAL hcosAL hgAL (by norm_num) (by norm_num)
                · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  norm_num
                all_goals norm_num [pairExpr]
              nlinarith [Real.pi_pos]
            ·
              have hroot1 : (1135359 / 500000 : ℝ) ≤ ‖y‖ := by
                apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (4301 / 4000 : ℝ) (1135359 / 500000 : ℝ)
                  (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
                norm_num
              have hroot2 : (586433 / 250000 : ℝ) ≤ ‖q‖ := by
                apply blocker_radius_ge_lower_root ‖z‖ ‖q‖ (4903 / 4000 : ℝ) (586433 / 250000 : ℝ)
                  (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hqsq
                norm_num
              exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
                (1135359 / 500000 : ℝ) (586433 / 250000 : ℝ) (69899 / 125000 : ℝ) (570671 / 1000000 : ℝ)
                hb (by linarith) (by norm_num) (by norm_num)
                hroot1 (by linarith) hroot2 (by linarith)
                hd0 hdpi he0 hepi hdlaw helaw
                (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (by norm_num [contactCos, sinCubicUpper])
                (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
      ·
        by_cases hcell8 : ‖z‖ ≤ (2301 / 2000 : ℝ)
        ·
          by_cases hcell9 : ‖a‖ ≤ (4903 / 4000 : ℝ)
          ·
            have hroot1 : (2307303 / 1000000 : ℝ) ≤ ‖y‖ := by
              apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (2301 / 2000 : ℝ) (2307303 / 1000000 : ℝ)
                (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
              norm_num
            have hcap : ‖q‖ ≤ (2281257 / 1000000 : ℝ) := by
              by_contra hcapNo
              exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
                (2307303 / 1000000 : ℝ) (2281257 / 1000000 : ℝ) (565071 / 1000000 : ℝ) (560943 / 1000000 : ℝ)
                hb (by linarith) (by norm_num) (by norm_num)
                hroot1 (by linarith) (by linarith) (by linarith)
                hd0 hdpi he0 hepi hdlaw helaw
                (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (by norm_num [contactCos, sinCubicUpper])
                (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
            have hangle0 : (22919 / 200 : ℝ) * Real.pi / 180 < gAA := by
              apply directed_pair_box_angle_gt_full a z gAA (22919 / 200 : ℝ) (-20810267 / 50000000 : ℝ)
                (2301 / 2000 : ℝ) (4903 / 4000 : ℝ) (1 : ℝ) (2301 / 2000 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepAA hcosAA hgAA (by norm_num) (by norm_num)
              · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                · norm_num
                · norm_num
              all_goals norm_num [pairExpr]
            have hangle1 : (30551 / 500 : ℝ) * Real.pi / 180 < gZH := by
              apply directed_pair_box_angle_gt_full z q gZH (30551 / 500 : ℝ) (12077407 / 25000000 : ℝ)
                (1 : ℝ) (2301 / 2000 : ℝ) (2 : ℝ) (2281257 / 1000000 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepZH hcosZH hgZH (by norm_num) (by norm_num)
              · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                norm_num
              all_goals norm_num [pairExpr]
            have hangle2 : (27611 / 500 : ℝ) * Real.pi / 180 < gHL := by
              apply directed_pair_box_angle_gt_full q l gHL (27611 / 500 : ℝ) (28515713 / 50000000 : ℝ)
                (2 : ℝ) (2281257 / 1000000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepHL hcosHL hgHL (by norm_num) (by norm_num)
              · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                norm_num
              all_goals norm_num [pairExpr]
            have hangle3 : (7213 / 100 : ℝ) * Real.pi / 180 < gAL := by
              apply directed_pair_box_angle_gt_full a t gAL (7213 / 100 : ℝ) (30643751 / 100000000 : ℝ)
                (2301 / 2000 : ℝ) (4903 / 4000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                (by norm_num) (by norm_num) (by linarith) (by linarith)
                (by linarith) (by linarith)
                hsepAL hcosAL hgAL (by norm_num) (by norm_num)
              · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                norm_num
              all_goals norm_num [pairExpr]
            nlinarith [Real.pi_pos]
          ·
            by_cases hcell10 : ‖z‖ ≤ (4301 / 4000 : ℝ)
            ·
              have hroot1 : (586433 / 250000 : ℝ) ≤ ‖y‖ := by
                apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (4903 / 4000 : ℝ) (586433 / 250000 : ℝ)
                  (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
                norm_num
              have hcap : ‖q‖ ≤ (140531 / 62500 : ℝ) := by
                by_contra hcapNo
                exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
                  (586433 / 250000 : ℝ) (140531 / 62500 : ℝ) (570671 / 1000000 : ℝ) (555343 / 1000000 : ℝ)
                  hb (by linarith) (by norm_num) (by norm_num)
                  hroot1 (by linarith) (by linarith) (by linarith)
                  hd0 hdpi he0 hepi hdlaw helaw
                  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  (by norm_num [contactCos, sinCubicUpper])
                  (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
              have hangle0 : (114297 / 1000 : ℝ) * Real.pi / 180 < gAA := by
                apply directed_pair_box_angle_gt_full a z gAA (114297 / 1000 : ℝ) (-4114791 / 10000000 : ℝ)
                  (4903 / 4000 : ℝ) (1301 / 1000 : ℝ) (1 : ℝ) (4301 / 4000 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepAA hcosAA hgAA (by norm_num) (by norm_num)
                · apply cos_obtuse_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  · norm_num
                  · norm_num
                all_goals norm_num [pairExpr]
              have hangle1 : (31383 / 500 : ℝ) * Real.pi / 180 < gZH := by
                apply directed_pair_box_angle_gt_full z q gZH (31383 / 500 : ℝ) (5717989 / 12500000 : ℝ)
                  (1 : ℝ) (4301 / 4000 : ℝ) (2 : ℝ) (140531 / 62500 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepZH hcosZH hgZH (by norm_num) (by norm_num)
                · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  norm_num
                all_goals norm_num [pairExpr]
              have hangle2 : (55791 / 1000 : ℝ) * Real.pi / 180 < gHL := by
                apply directed_pair_box_angle_gt_full q l gHL (55791 / 1000 : ℝ) (56212401 / 100000000 : ℝ)
                  (2 : ℝ) (140531 / 62500 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepHL hcosHL hgHL (by norm_num) (by norm_num)
                · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  norm_num
                all_goals norm_num [pairExpr]
              have hangle3 : (17749 / 250 : ℝ) * Real.pi / 180 < gAL := by
                apply directed_pair_box_angle_gt_full a t gAL (17749 / 250 : ℝ) (32525001 / 100000000 : ℝ)
                  (4903 / 4000 : ℝ) (1301 / 1000 : ℝ) (3 / 2 : ℝ) (2 : ℝ)
                  (by norm_num) (by norm_num) (by linarith) (by linarith)
                  (by linarith) (by linarith)
                  hsepAL hcosAL hgAL (by norm_num) (by norm_num)
                · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
                  norm_num
                all_goals norm_num [pairExpr]
              nlinarith [Real.pi_pos]
            ·
              have hroot1 : (586433 / 250000 : ℝ) ≤ ‖y‖ := by
                apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (4903 / 4000 : ℝ) (586433 / 250000 : ℝ)
                  (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
                norm_num
              have hroot2 : (1135359 / 500000 : ℝ) ≤ ‖q‖ := by
                apply blocker_radius_ge_lower_root ‖z‖ ‖q‖ (4301 / 4000 : ℝ) (1135359 / 500000 : ℝ)
                  (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hqsq
                norm_num
              exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
                (586433 / 250000 : ℝ) (1135359 / 500000 : ℝ) (570671 / 1000000 : ℝ) (69899 / 125000 : ℝ)
                hb (by linarith) (by norm_num) (by norm_num)
                hroot1 (by linarith) hroot2 (by linarith)
                hd0 hdpi he0 hepi hdlaw helaw
                (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (by norm_num [contactCos, sinCubicUpper])
                (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
        ·
          have hroot1 : (2307303 / 1000000 : ℝ) ≤ ‖y‖ := by
            apply blocker_radius_ge_lower_root ‖a‖ ‖y‖ (2301 / 2000 : ℝ) (2307303 / 1000000 : ℝ)
              (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hysq
            norm_num
          have hroot2 : (2307303 / 1000000 : ℝ) ≤ ‖q‖ := by
            apply blocker_radius_ge_lower_root ‖z‖ ‖q‖ (2301 / 2000 : ℝ) (2307303 / 1000000 : ℝ)
              (by norm_num) (by linarith) (norm_nonneg _) (by norm_num) hqsq
            norm_num
          exact two_contact_rational_support_impossible b ‖y‖ ‖q‖ d e
            (2307303 / 1000000 : ℝ) (2307303 / 1000000 : ℝ) (565071 / 1000000 : ℝ) (565071 / 1000000 : ℝ)
            hb (by linarith) (by norm_num) (by norm_num)
            hroot1 (by linarith) hroot2 (by linarith)
            hd0 hdpi he0 hepi hdlaw helaw
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num [contactCos, sinCubicUpper])
            (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget

end CP15
