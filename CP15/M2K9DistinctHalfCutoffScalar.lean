import CP15.M2K9DistinctCutoff

open scoped InnerProductSpace

namespace CP15

set_option maxHeartbeats 0

/-- A correlated core-radius cell. Each displayed numerical premise is
proved by exact rational arithmetic in the generated cover below. -/
private theorem distinct_half_cutoff_cell
    (b r t s z d e l u sl zl a c : ℝ)
    (hb3 : 3 < b) (hb7 : b ≤ 7 / 2)
    (hsl : 2 < sl) (hzl : 2 < zl)
    (hl0 : 0 ≤ l) (hu2 : u ≤ 2)
    (hrl : l ≤ r) (hru : r ≤ u) (ht0 : 0 ≤ t)
    (hrt : 2 ≤ r + t)
    (hs2 : 2 < s) (hsU : s ≤ 12 / 5)
    (hz2 : 2 < z) (hzU : z ≤ 12 / 5)
    (hssq : 4 + r ^ 2 < s ^ 2) (hzsq : 4 + t ^ 2 < z ^ 2)
    (hslcert : sl ^ 2 ≤ 4 + l ^ 2)
    (hzlcert : zl ^ 2 ≤ 4 + (2 - u) ^ 2)
    (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi)
    (he0 : 0 ≤ e) (hepi : e ≤ Real.pi)
    (hdlaw : 2 * s * b * Real.cos d = b ^ 2 + s ^ 2 - 4)
    (helaw : 2 * z * b * Real.cos e = b ^ 2 + z ^ 2 - 4)
    (ha : 0 ≤ a ∧ a ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hacert : contactCos (7 / 2) sl < 1 - 2 * sinCubicUpper (a / 2) ^ 2)
    (hccert : contactCos (7 / 2) zl < 1 - 2 * sinCubicUpper (c / 2) ^ 2)
    (hsum : 2 * a + 2 * c + 7 * (57949 / 100000 : ℝ) >
      2 * (3141593 / 1000000 : ℝ))
    (hbudget : 2 * d + 2 * e + 7 * (57949 / 100000 : ℝ) ≤
      2 * Real.pi) : False := by
  have hr0 : 0 ≤ r := hl0.trans hrl
  have htlo : 2 - u ≤ t := by linarith
  have hslower : sl ≤ s := by nlinarith
  have hzlower : zl ≤ z := by nlinarith
  have hd := contact_offset_gt_rational_angle b (7 / 2) sl s d a
    hb3 hb7 (by norm_num) (by linarith) hslower hsU
    hd0 hdpi ha.1 ha.2 hacert hdlaw
  have he := contact_offset_gt_rational_angle b (7 / 2) zl z e c
    hb3 hb7 (by norm_num) (by linarith) hzlower hzU
    he0 hepi hc.1 hc.2 hccert helaw
  linarith [Real.pi_lt_d6]

/-- Sixteen closed rational cells cover the whole correlated domain.
The producer only proposes numbers: `norm_num` checks all corner tests
and margins in the Lean kernel, and `by_cases` establishes coverage. -/
theorem distinct_half_cutoff_scalar_certificate
    (b r t s z d e : ℝ)
    (hb3 : 3 < b) (hb7 : b ≤ 7 / 2)
    (hr1 : 1 ≤ r) (hrU : r ≤ 5 / 4) (ht0 : 0 ≤ t)
    (hrt : 2 ≤ r + t)
    (hs2 : 2 < s) (hsU : s ≤ 12 / 5)
    (hz2 : 2 < z) (hzU : z ≤ 12 / 5)
    (hssq : 4 + r ^ 2 < s ^ 2) (hzsq : 4 + t ^ 2 < z ^ 2)
    (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi)
    (he0 : 0 ≤ e) (hepi : e ≤ Real.pi)
    (hdlaw : 2 * s * b * Real.cos d = b ^ 2 + s ^ 2 - 4)
    (helaw : 2 * z * b * Real.cos e = b ^ 2 + z ^ 2 - 4)
    (hbudget : 2 * d + 2 * e + 7 * (57949 / 100000 : ℝ) ≤
      2 * Real.pi) : False := by
  by_cases h0 : r ≤ (65 / 64 : ℝ)
  · exact distinct_half_cutoff_cell b r t s z d e
      (1 / 1 : ℝ) (65 / 64 : ℝ) (111803 / 50000 : ℝ) (6966 / 3125 : ℝ) (56139 / 100000 : ℝ) (3501 / 6250 : ℝ)
      hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
      (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
      (by constructor <;> norm_num) (by constructor <;> norm_num)
      (by norm_num [contactCos, sinCubicUpper])
      (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
  ·
    by_cases h1 : r ≤ (33 / 32 : ℝ)
    · exact distinct_half_cutoff_cell b r t s z d e
        (65 / 64 : ℝ) (33 / 32 : ℝ) (224309 / 100000 : ℝ) (111113 / 50000 : ℝ) (2813 / 5000 : ℝ) (27947 / 50000 : ℝ)
        hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
        (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by norm_num [contactCos, sinCubicUpper])
        (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
    ·
      by_cases h2 : r ≤ (67 / 64 : ℝ)
      · exact distinct_half_cutoff_cell b r t s z d e
          (33 / 32 : ℝ) (67 / 64 : ℝ) (225021 / 100000 : ℝ) (4431 / 2000 : ℝ) (56381 / 100000 : ℝ) (5577 / 10000 : ℝ)
          hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
          (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
          (by constructor <;> norm_num) (by constructor <;> norm_num)
          (by norm_num [contactCos, sinCubicUpper])
          (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
      ·
        by_cases h3 : r ≤ (17 / 16 : ℝ)
        · exact distinct_half_cutoff_cell b r t s z d e
            (67 / 64 : ℝ) (17 / 16 : ℝ) (112871 / 50000 : ℝ) (110441 / 50000 : ℝ) (56501 / 100000 : ℝ) (55647 / 100000 : ℝ)
            hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
            (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
            (by constructor <;> norm_num) (by constructor <;> norm_num)
            (by norm_num [contactCos, sinCubicUpper])
            (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
        ·
          by_cases h4 : r ≤ (69 / 64 : ℝ)
          · exact distinct_half_cutoff_cell b r t s z d e
              (17 / 16 : ℝ) (69 / 64 : ℝ) (22647 / 10000 : ℝ) (220223 / 100000 : ℝ) (2831 / 5000 : ℝ) (55523 / 100000 : ℝ)
              hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
              (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
              (by constructor <;> norm_num) (by constructor <;> norm_num)
              (by norm_num [contactCos, sinCubicUpper])
              (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
          ·
            by_cases h5 : r ≤ (35 / 32 : ℝ)
            · exact distinct_half_cutoff_cell b r t s z d e
                (69 / 64 : ℝ) (35 / 32 : ℝ) (28401 / 12500 : ℝ) (109787 / 50000 : ℝ) (56739 / 100000 : ℝ) (27699 / 50000 : ℝ)
                hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                (by constructor <;> norm_num) (by constructor <;> norm_num)
                (by norm_num [contactCos, sinCubicUpper])
                (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
            ·
              by_cases h6 : r ≤ (71 / 64 : ℝ)
              · exact distinct_half_cutoff_cell b r t s z d e
                  (35 / 32 : ℝ) (71 / 64 : ℝ) (227953 / 100000 : ℝ) (109467 / 50000 : ℝ) (7107 / 12500 : ℝ) (27637 / 50000 : ℝ)
                  hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                  (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                  (by constructor <;> norm_num) (by constructor <;> norm_num)
                  (by norm_num [contactCos, sinCubicUpper])
                  (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
              ·
                by_cases h7 : r ≤ (9 / 8 : ℝ)
                · exact distinct_half_cutoff_cell b r t s z d e
                    (71 / 64 : ℝ) (9 / 8 : ℝ) (228707 / 100000 : ℝ) (218303 / 100000 : ℝ) (14243 / 25000 : ℝ) (55149 / 100000 : ℝ)
                    hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                    (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                    (by constructor <;> norm_num) (by constructor <;> norm_num)
                    (by norm_num [contactCos, sinCubicUpper])
                    (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                ·
                  by_cases h8 : r ≤ (73 / 64 : ℝ)
                  · exact distinct_half_cutoff_cell b r t s z d e
                      (9 / 8 : ℝ) (73 / 64 : ℝ) (229469 / 100000 : ℝ) (217681 / 100000 : ℝ) (1784 / 3125 : ℝ) (3439 / 6250 : ℝ)
                      hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                      (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                      (by constructor <;> norm_num) (by constructor <;> norm_num)
                      (by norm_num [contactCos, sinCubicUpper])
                      (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                  ·
                    by_cases h9 : r ≤ (37 / 32 : ℝ)
                    · exact distinct_half_cutoff_cell b r t s z d e
                        (73 / 64 : ℝ) (37 / 32 : ℝ) (230239 / 100000 : ℝ) (217069 / 100000 : ℝ) (28601 / 50000 : ℝ) (54899 / 100000 : ℝ)
                        hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                        (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                        (by constructor <;> norm_num) (by constructor <;> norm_num)
                        (by norm_num [contactCos, sinCubicUpper])
                        (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                    ·
                      by_cases h10 : r ≤ (75 / 64 : ℝ)
                      · exact distinct_half_cutoff_cell b r t s z d e
                          (37 / 32 : ℝ) (75 / 64 : ℝ) (231017 / 100000 : ℝ) (108233 / 50000 : ℝ) (11463 / 20000 : ℝ) (27387 / 50000 : ℝ)
                          hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                          (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                          (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                          (by constructor <;> norm_num) (by constructor <;> norm_num)
                          (by norm_num [contactCos, sinCubicUpper])
                          (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                      ·
                        by_cases h11 : r ≤ (19 / 16 : ℝ)
                        · exact distinct_half_cutoff_cell b r t s z d e
                            (75 / 64 : ℝ) (19 / 16 : ℝ) (231803 / 100000 : ℝ) (215873 / 100000 : ℝ) (57427 / 100000 : ℝ) (1093 / 2000 : ℝ)
                            hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                            (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                            (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                            (by constructor <;> norm_num) (by constructor <;> norm_num)
                            (by norm_num [contactCos, sinCubicUpper])
                            (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                        ·
                          by_cases h12 : r ≤ (77 / 64 : ℝ)
                          · exact distinct_half_cutoff_cell b r t s z d e
                              (19 / 16 : ℝ) (77 / 64 : ℝ) (232597 / 100000 : ℝ) (21529 / 10000 : ℝ) (57537 / 100000 : ℝ) (2181 / 4000 : ℝ)
                              hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                              (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                              (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                              (by constructor <;> norm_num) (by constructor <;> norm_num)
                              (by norm_num [contactCos, sinCubicUpper])
                              (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                          ·
                            by_cases h13 : r ≤ (39 / 32 : ℝ)
                            · exact distinct_half_cutoff_cell b r t s z d e
                                (77 / 64 : ℝ) (39 / 32 : ℝ) (233399 / 100000 : ℝ) (214717 / 100000 : ℝ) (57647 / 100000 : ℝ) (54401 / 100000 : ℝ)
                                hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                                (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                                (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                                (by constructor <;> norm_num) (by constructor <;> norm_num)
                                (by norm_num [contactCos, sinCubicUpper])
                                (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                            ·
                              by_cases h14 : r ≤ (79 / 64 : ℝ)
                              · exact distinct_half_cutoff_cell b r t s z d e
                                  (39 / 32 : ℝ) (79 / 64 : ℝ) (7319 / 3125 : ℝ) (214153 / 100000 : ℝ) (11551 / 20000 : ℝ) (54277 / 100000 : ℝ)
                                  hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                                  (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                                  (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                                  (by constructor <;> norm_num) (by constructor <;> norm_num)
                                  (by norm_num [contactCos, sinCubicUpper])
                                  (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget
                              ·
                                exact distinct_half_cutoff_cell b r t s z d e
                                  (79 / 64 : ℝ) (5 / 4 : ℝ) (9401 / 4000 : ℝ) (267 / 125 : ℝ) (57861 / 100000 : ℝ) (27077 / 50000 : ℝ)
                                  hb3 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                                  (by linarith) (by linarith) ht0 hrt hs2 hsU hz2 hzU hssq hzsq
                                  (by norm_num) (by norm_num) hd0 hdpi he0 hepi hdlaw helaw
                                  (by constructor <;> norm_num) (by constructor <;> norm_num)
                                  (by norm_num [contactCos, sinCubicUpper])
                                  (by norm_num [contactCos, sinCubicUpper]) (by norm_num) hbudget

end CP15
