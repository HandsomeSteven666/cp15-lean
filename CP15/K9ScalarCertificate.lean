import CP15.K9ScalarBounds

set_option maxHeartbeats 0

namespace CP15

/-- Exact rational 64-cell cover of the shared-blocker K=9 scalar
budget. The generated cases partition `[23094/10000, 238544/100000]`
without gaps. Each cell is closed by kernel-checked rational arithmetic. -/
theorem k9_scalar_64_cell_certificate
    (b s z r δ₁ δ₂ : ℝ)
    (hb3 : 3 < b) (hbB : b ≤ (352136 / 100000 : ℝ))
    (hb12 : 12 < b ^ 2)
    (hs2 : 2 < s) (hslow : (11547 / 5000 : ℝ) ≤ s)
    (hshigh : s ≤ (14909 / 6250 : ℝ))
    (hz2 : 2 < z) (hzhi : z ≤ 12 / 5)
    (hrlower : 8 / s - s < r) (hzsq : 4 + r ^ 2 < z ^ 2)
    (hδ₁0 : 0 ≤ δ₁) (hδ₁pi : δ₁ ≤ Real.pi)
    (hδ₂0 : 0 ≤ δ₂) (hδ₂pi : δ₂ ≤ Real.pi)
    (hlaw₁ : 2 * s * b * Real.cos δ₁ = b ^ 2 + s ^ 2 - 4)
    (hlaw₂ : 2 * z * b * Real.cos δ₂ = b ^ 2 + z ^ 2 - 4)
    (hbudget : 2 * δ₁ + 2 * δ₂ + 7 * (57588 / 100000 : ℝ) ≤
      2 * Real.pi) : False := by
  by_cases h0 : s ≤ (3696941 / 1600000 : ℝ)
  ·
    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
      (11547 / 5000 : ℝ) (3696941 / 1600000 : ℝ) (46158383 / 20000000 : ℝ)
      (56539211 / 100000000 : ℝ) (28258301 / 50000000 : ℝ)
      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
      hlaw₁ hlaw₂ (by constructor <;> norm_num)
      (by constructor <;> norm_num)
      (by norm_num [contactCos, sinCubicUpper])
      (by norm_num [contactCos, sinCubicUpper])
      (by norm_num) hbudget
  ·
    by_cases h1 : s ≤ (1849421 / 800000 : ℝ)
    ·
      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
        (3696941 / 1600000 : ℝ) (1849421 / 800000 : ℝ) (115321983 / 50000000 : ℝ)
        (7069661 / 12500000 : ℝ) (28246963 / 50000000 : ℝ)
        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
        hlaw₁ hlaw₂ (by constructor <;> norm_num)
        (by constructor <;> norm_num)
        (by norm_num [contactCos, sinCubicUpper])
        (by norm_num [contactCos, sinCubicUpper])
        (by norm_num) hbudget
    ·
      by_cases h2 : s ≤ (3700743 / 1600000 : ℝ)
      ·
        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
          (1849421 / 800000 : ℝ) (3700743 / 1600000 : ℝ) (46099279 / 20000000 : ℝ)
          (56575309 / 100000000 : ℝ) (56471221 / 100000000 : ℝ)
          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
          hlaw₁ hlaw₂ (by constructor <;> norm_num)
          (by constructor <;> norm_num)
          (by norm_num [contactCos, sinCubicUpper])
          (by norm_num [contactCos, sinCubicUpper])
          (by norm_num) hbudget
      ·
        by_cases h3 : s ≤ (925661 / 400000 : ℝ)
        ·
          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
            (3700743 / 1600000 : ℝ) (925661 / 400000 : ℝ) (115174601 / 50000000 : ℝ)
            (28296637 / 50000000 : ℝ) (28224243 / 50000000 : ℝ)
            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
            hlaw₁ hlaw₂ (by constructor <;> norm_num)
            (by constructor <;> norm_num)
            (by norm_num [contactCos, sinCubicUpper])
            (by norm_num [contactCos, sinCubicUpper])
            (by norm_num) hbudget
        ·
          by_cases h4 : s ≤ (740909 / 320000 : ℝ)
          ·
            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
              (925661 / 400000 : ℝ) (740909 / 320000 : ℝ) (230202387 / 100000000 : ℝ)
              (56611183 / 100000000 : ℝ) (14106431 / 25000000 : ℝ)
              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
              hlaw₁ hlaw₂ (by constructor <;> norm_num)
              (by constructor <;> norm_num)
              (by norm_num [contactCos, sinCubicUpper])
              (by norm_num [contactCos, sinCubicUpper])
              (by norm_num) hbudget
          ·
            by_cases h5 : s ≤ (1853223 / 800000 : ℝ)
            ·
              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                (740909 / 320000 : ℝ) (1853223 / 800000 : ℝ) (4601119 / 2000000 : ℝ)
                (14157259 / 25000000 : ℝ) (56402933 / 100000000 : ℝ)
                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                (by constructor <;> norm_num)
                (by norm_num [contactCos, sinCubicUpper])
                (by norm_num [contactCos, sinCubicUpper])
                (by norm_num) hbudget
            ·
              by_cases h6 : s ≤ (3708347 / 1600000 : ℝ)
              ·
                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                  (1853223 / 800000 : ℝ) (3708347 / 1600000 : ℝ) (229909889 / 100000000 : ℝ)
                  (28323417 / 50000000 : ℝ) (28190057 / 50000000 : ℝ)
                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                  (by constructor <;> norm_num)
                  (by norm_num [contactCos, sinCubicUpper])
                  (by norm_num [contactCos, sinCubicUpper])
                  (by norm_num) hbudget
              ·
                by_cases h7 : s ≤ (463781 / 200000 : ℝ)
                ·
                  exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                    (3708347 / 1600000 : ℝ) (463781 / 200000 : ℝ) (229764207 / 100000000 : ℝ)
                    (56664577 / 100000000 : ℝ) (14089317 / 25000000 : ℝ)
                    hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                    (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                    (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                    hlaw₁ hlaw₂ (by constructor <;> norm_num)
                    (by constructor <;> norm_num)
                    (by norm_num [contactCos, sinCubicUpper])
                    (by norm_num [contactCos, sinCubicUpper])
                    (by norm_num) hbudget
                ·
                  by_cases h8 : s ≤ (3712149 / 1600000 : ℝ)
                  ·
                    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                      (463781 / 200000 : ℝ) (3712149 / 1600000 : ℝ) (229618901 / 100000000 : ℝ)
                      (7085283 / 12500000 : ℝ) (11266879 / 20000000 : ℝ)
                      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                      hlaw₁ hlaw₂ (by constructor <;> norm_num)
                      (by constructor <;> norm_num)
                      (by norm_num [contactCos, sinCubicUpper])
                      (by norm_num [contactCos, sinCubicUpper])
                      (by norm_num) hbudget
                  ·
                    by_cases h9 : s ≤ (74281 / 32000 : ℝ)
                    ·
                      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                        (3712149 / 1600000 : ℝ) (74281 / 32000 : ℝ) (229473973 / 100000000 : ℝ)
                        (7087487 / 12500000 : ℝ) (7038937 / 12500000 : ℝ)
                        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                        hlaw₁ hlaw₂ (by constructor <;> norm_num)
                        (by constructor <;> norm_num)
                        (by norm_num [contactCos, sinCubicUpper])
                        (by norm_num [contactCos, sinCubicUpper])
                        (by norm_num) hbudget
                    ·
                      by_cases h10 : s ≤ (3715951 / 1600000 : ℝ)
                      ·
                        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                          (74281 / 32000 : ℝ) (3715951 / 1600000 : ℝ) (114664711 / 50000000 : ℝ)
                          (56717473 / 100000000 : ℝ) (5628857 / 10000000 : ℝ)
                          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                          hlaw₁ hlaw₂ (by constructor <;> norm_num)
                          (by constructor <;> norm_num)
                          (by norm_num [contactCos, sinCubicUpper])
                          (by norm_num [contactCos, sinCubicUpper])
                          (by norm_num) hbudget
                      ·
                        by_cases h11 : s ≤ (929463 / 400000 : ℝ)
                        ·
                          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                            (3715951 / 1600000 : ℝ) (929463 / 400000 : ℝ) (229185247 / 100000000 : ℝ)
                            (28367497 / 50000000 : ℝ) (56265619 / 100000000 : ℝ)
                            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                            hlaw₁ hlaw₂ (by constructor <;> norm_num)
                            (by constructor <;> norm_num)
                            (by norm_num [contactCos, sinCubicUpper])
                            (by norm_num [contactCos, sinCubicUpper])
                            (by norm_num) hbudget
                        ·
                          by_cases h12 : s ≤ (3719753 / 1600000 : ℝ)
                          ·
                            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                              (929463 / 400000 : ℝ) (3719753 / 1600000 : ℝ) (4580829 / 2000000 : ℝ)
                              (56752461 / 100000000 : ℝ) (28121321 / 50000000 : ℝ)
                              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                              hlaw₁ hlaw₂ (by constructor <;> norm_num)
                              (by constructor <;> norm_num)
                              (by norm_num [contactCos, sinCubicUpper])
                              (by norm_num [contactCos, sinCubicUpper])
                              (by norm_num) hbudget
                          ·
                            by_cases h13 : s ≤ (1860827 / 800000 : ℝ)
                            ·
                              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                (3719753 / 1600000 : ℝ) (1860827 / 800000 : ℝ) (228898029 / 100000000 : ℝ)
                                (28384937 / 50000000 : ℝ) (56219641 / 100000000 : ℝ)
                                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                (by constructor <;> norm_num)
                                (by norm_num [contactCos, sinCubicUpper])
                                (by norm_num [contactCos, sinCubicUpper])
                                (by norm_num) hbudget
                            ·
                              by_cases h14 : s ≤ (744711 / 320000 : ℝ)
                              ·
                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                  (1860827 / 800000 : ℝ) (744711 / 320000 : ℝ) (28594373 / 12500000 : ℝ)
                                  (1774601 / 3125000 : ℝ) (11239323 / 20000000 : ℝ)
                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                  (by constructor <;> norm_num)
                                  (by norm_num [contactCos, sinCubicUpper])
                                  (by norm_num [contactCos, sinCubicUpper])
                                  (by norm_num) hbudget
                              ·
                                by_cases h15 : s ≤ (232841 / 100000 : ℝ)
                                ·
                                  exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                    (744711 / 320000 : ℝ) (232841 / 100000 : ℝ) (57153079 / 25000000 : ℝ)
                                    (11360907 / 20000000 : ℝ) (11234713 / 20000000 : ℝ)
                                    hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                    (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                    (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                    hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                    (by constructor <;> norm_num)
                                    (by norm_num [contactCos, sinCubicUpper])
                                    (by norm_num [contactCos, sinCubicUpper])
                                    (by norm_num) hbudget
                                ·
                                  by_cases h16 : s ≤ (3727357 / 1600000 : ℝ)
                                  ·
                                    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                      (232841 / 100000 : ℝ) (3727357 / 1600000 : ℝ) (9138801 / 4000000 : ℝ)
                                      (7102723 / 12500000 : ℝ) (56150491 / 100000000 : ℝ)
                                      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                      hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                      (by constructor <;> norm_num)
                                      (by norm_num [contactCos, sinCubicUpper])
                                      (by norm_num [contactCos, sinCubicUpper])
                                      (by norm_num) hbudget
                                  ·
                                    by_cases h17 : s ≤ (1864629 / 800000 : ℝ)
                                    ·
                                      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                        (3727357 / 1600000 : ℝ) (1864629 / 800000 : ℝ) (228328109 / 100000000 : ℝ)
                                        (56838979 / 100000000 : ℝ) (11225479 / 20000000 : ℝ)
                                        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                        hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                        (by constructor <;> norm_num)
                                        (by norm_num [contactCos, sinCubicUpper])
                                        (by norm_num [contactCos, sinCubicUpper])
                                        (by norm_num) hbudget
                                    ·
                                      by_cases h18 : s ≤ (3731159 / 1600000 : ℝ)
                                      ·
                                        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                          (1864629 / 800000 : ℝ) (3731159 / 1600000 : ℝ) (22818657 / 10000000 : ℝ)
                                          (56856119 / 100000000 : ℝ) (2244171 / 4000000 : ℝ)
                                          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                          hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                          (by constructor <;> norm_num)
                                          (by norm_num [contactCos, sinCubicUpper])
                                          (by norm_num [contactCos, sinCubicUpper])
                                          (by norm_num) hbudget
                                      ·
                                        by_cases h19 : s ≤ (186653 / 80000 : ℝ)
                                        ·
                                          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                            (3731159 / 1600000 : ℝ) (186653 / 80000 : ℝ) (114022703 / 50000000 : ℝ)
                                            (28436603 / 50000000 : ℝ) (56081133 / 100000000 : ℝ)
                                            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                            hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                            (by constructor <;> norm_num)
                                            (by norm_num [contactCos, sinCubicUpper])
                                            (by norm_num [contactCos, sinCubicUpper])
                                            (by norm_num) hbudget
                                        ·
                                          by_cases h20 : s ≤ (3734961 / 1600000 : ℝ)
                                          ·
                                            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                              (186653 / 80000 : ℝ) (3734961 / 1600000 : ℝ) (227904619 / 100000000 : ℝ)
                                              (56890239 / 100000000 : ℝ) (56057969 / 100000000 : ℝ)
                                              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                              hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                              (by constructor <;> norm_num)
                                              (by norm_num [contactCos, sinCubicUpper])
                                              (by norm_num [contactCos, sinCubicUpper])
                                              (by norm_num) hbudget
                                          ·
                                            by_cases h21 : s ≤ (1868431 / 800000 : ℝ)
                                            ·
                                              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                (3734961 / 1600000 : ℝ) (1868431 / 800000 : ℝ) (227764207 / 100000000 : ℝ)
                                                (28453609 / 50000000 : ℝ) (1751087 / 3125000 : ℝ)
                                                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                (by constructor <;> norm_num)
                                                (by norm_num [contactCos, sinCubicUpper])
                                                (by norm_num [contactCos, sinCubicUpper])
                                                (by norm_num) hbudget
                                            ·
                                              by_cases h22 : s ≤ (3738763 / 1600000 : ℝ)
                                              ·
                                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                  (1868431 / 800000 : ℝ) (3738763 / 1600000 : ℝ) (227624171 / 100000000 : ℝ)
                                                  (3557759 / 6250000 : ℝ) (56011577 / 100000000 : ℝ)
                                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                  (by constructor <;> norm_num)
                                                  (by norm_num [contactCos, sinCubicUpper])
                                                  (by norm_num [contactCos, sinCubicUpper])
                                                  (by norm_num) hbudget
                                              ·
                                                by_cases h23 : s ≤ (467583 / 200000 : ℝ)
                                                ·
                                                  exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                    (3738763 / 1600000 : ℝ) (467583 / 200000 : ℝ) (22748451 / 10000000 : ℝ)
                                                    (7117627 / 12500000 : ℝ) (1119767 / 2000000 : ℝ)
                                                    hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                    (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                    (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                    hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                    (by constructor <;> norm_num)
                                                    (by norm_num [contactCos, sinCubicUpper])
                                                    (by norm_num [contactCos, sinCubicUpper])
                                                    (by norm_num) hbudget
                                                ·
                                                  by_cases h24 : s ≤ (748513 / 320000 : ℝ)
                                                  ·
                                                    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                      (467583 / 200000 : ℝ) (748513 / 320000 : ℝ) (28418153 / 12500000 : ℝ)
                                                      (28478917 / 50000000 : ℝ) (27982551 / 50000000 : ℝ)
                                                      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                      hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                      (by constructor <;> norm_num)
                                                      (by norm_num [contactCos, sinCubicUpper])
                                                      (by norm_num [contactCos, sinCubicUpper])
                                                      (by norm_num) hbudget
                                                  ·
                                                    by_cases h25 : s ≤ (1872233 / 800000 : ℝ)
                                                    ·
                                                      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                        (748513 / 320000 : ℝ) (1872233 / 800000 : ℝ) (113603157 / 50000000 : ℝ)
                                                        (284873 / 500000 : ℝ) (11188367 / 20000000 : ℝ)
                                                        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                        hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                        (by constructor <;> norm_num)
                                                        (by norm_num [contactCos, sinCubicUpper])
                                                        (by norm_num [contactCos, sinCubicUpper])
                                                        (by norm_num) hbudget
                                                    ·
                                                      by_cases h26 : s ≤ (3746367 / 1600000 : ℝ)
                                                      ·
                                                        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                          (1872233 / 800000 : ℝ) (3746367 / 1600000 : ℝ) (227067779 / 100000000 : ℝ)
                                                          (3561957 / 6250000 : ℝ) (13979637 / 25000000 : ℝ)
                                                          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                          hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                          (by constructor <;> norm_num)
                                                          (by norm_num [contactCos, sinCubicUpper])
                                                          (by norm_num [contactCos, sinCubicUpper])
                                                          (by norm_num) hbudget
                                                      ·
                                                        by_cases h27 : s ≤ (937067 / 400000 : ℝ)
                                                        ·
                                                          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                            (3746367 / 1600000 : ℝ) (937067 / 400000 : ℝ) (113464809 / 50000000 : ℝ)
                                                            (57007971 / 100000000 : ℝ) (27947621 / 50000000 : ℝ)
                                                            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                            hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                            (by constructor <;> norm_num)
                                                            (by norm_num [contactCos, sinCubicUpper])
                                                            (by norm_num [contactCos, sinCubicUpper])
                                                            (by norm_num) hbudget
                                                        ·
                                                          by_cases h28 : s ≤ (3750169 / 1600000 : ℝ)
                                                          ·
                                                            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                              (937067 / 400000 : ℝ) (3750169 / 1600000 : ℝ) (226791833 / 100000000 : ℝ)
                                                              (57024577 / 100000000 : ℝ) (55871917 / 100000000 : ℝ)
                                                              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                              hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                              (by constructor <;> norm_num)
                                                              (by norm_num [contactCos, sinCubicUpper])
                                                              (by norm_num [contactCos, sinCubicUpper])
                                                              (by norm_num) hbudget
                                                          ·
                                                            by_cases h29 : s ≤ (375207 / 160000 : ℝ)
                                                            ·
                                                              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                (3750169 / 1600000 : ℝ) (375207 / 160000 : ℝ) (113327211 / 50000000 : ℝ)
                                                                (57041131 / 100000000 : ℝ) (27924287 / 50000000 : ℝ)
                                                                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                (by constructor <;> norm_num)
                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                (by norm_num) hbudget
                                                            ·
                                                              by_cases h30 : s ≤ (3753971 / 1600000 : ℝ)
                                                              ·
                                                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                  (375207 / 160000 : ℝ) (3753971 / 1600000 : ℝ) (113258693 / 50000000 : ℝ)
                                                                  (1783051 / 3125000 : ℝ) (27912607 / 50000000 : ℝ)
                                                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                  (by constructor <;> norm_num)
                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                  (by norm_num) hbudget
                                                              ·
                                                                by_cases h31 : s ≤ (117371 / 50000 : ℝ)
                                                                ·
                                                                  exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                    (3753971 / 1600000 : ℝ) (117371 / 50000 : ℝ) (9055229 / 4000000 : ℝ)
                                                                    (356713 / 625000 : ℝ) (13950459 / 25000000 : ℝ)
                                                                    hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                    (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                    (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                    hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                    (by constructor <;> norm_num)
                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                    (by norm_num) hbudget
                                                                ·
                                                                  by_cases h32 : s ≤ (3757773 / 1600000 : ℝ)
                                                                  ·
                                                                    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                      (117371 / 50000 : ℝ) (3757773 / 1600000 : ℝ) (113122219 / 50000000 : ℝ)
                                                                      (2283619 / 4000000 : ℝ) (55778441 / 100000000 : ℝ)
                                                                      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                      hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                      (by constructor <;> norm_num)
                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                      (by norm_num) hbudget
                                                                  ·
                                                                    by_cases h33 : s ≤ (1879837 / 800000 : ℝ)
                                                                    ·
                                                                      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                        (3757773 / 1600000 : ℝ) (1879837 / 800000 : ℝ) (9044341 / 4000000 : ℝ)
                                                                        (57106819 / 100000000 : ℝ) (5575503 / 10000000 : ℝ)
                                                                        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                        hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                        (by constructor <;> norm_num)
                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                        (by norm_num) hbudget
                                                                    ·
                                                                      by_cases h34 : s ≤ (150463 / 64000 : ℝ)
                                                                      ·
                                                                        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                          (1879837 / 800000 : ℝ) (150463 / 64000 : ℝ) (112986493 / 50000000 : ℝ)
                                                                          (5712311 / 10000000 : ℝ) (27865801 / 50000000 : ℝ)
                                                                          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                          hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                          (by constructor <;> norm_num)
                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                          (by norm_num) hbudget
                                                                      ·
                                                                        by_cases h35 : s ≤ (940869 / 400000 : ℝ)
                                                                        ·
                                                                          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                            (150463 / 64000 : ℝ) (940869 / 400000 : ℝ) (112918911 / 50000000 : ℝ)
                                                                            (57139349 / 100000000 : ℝ) (55708159 / 100000000 : ℝ)
                                                                            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                            hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                            (by constructor <;> norm_num)
                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                            (by norm_num) hbudget
                                                                        ·
                                                                          by_cases h36 : s ≤ (3765377 / 1600000 : ℝ)
                                                                          ·
                                                                            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                              (940869 / 400000 : ℝ) (3765377 / 1600000 : ℝ) (225703031 / 100000000 : ℝ)
                                                                              (3572221 / 6250000 : ℝ) (55684701 / 100000000 : ℝ)
                                                                              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                              hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                              (by constructor <;> norm_num)
                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                              (by norm_num) hbudget
                                                                          ·
                                                                            by_cases h37 : s ≤ (1883639 / 800000 : ℝ)
                                                                            ·
                                                                              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                (3765377 / 1600000 : ℝ) (1883639 / 800000 : ℝ) (112784307 / 50000000 : ℝ)
                                                                                (57171671 / 100000000 : ℝ) (13915307 / 25000000 : ℝ)
                                                                                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                (by constructor <;> norm_num)
                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                (by norm_num) hbudget
                                                                            ·
                                                                              by_cases h38 : s ≤ (3769179 / 1600000 : ℝ)
                                                                              ·
                                                                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                  (1883639 / 800000 : ℝ) (3769179 / 1600000 : ℝ) (22543457 / 10000000 : ℝ)
                                                                                  (11437551 / 20000000 : ℝ) (2781887 / 5000000 : ℝ)
                                                                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                  (by constructor <;> norm_num)
                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                  (by norm_num) hbudget
                                                                              ·
                                                                                by_cases h39 : s ≤ (94277 / 40000 : ℝ)
                                                                                ·
                                                                                  exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                    (3769179 / 1600000 : ℝ) (94277 / 40000 : ℝ) (2253009 / 1000000 : ℝ)
                                                                                    (28601893 / 50000000 : ℝ) (55614239 / 100000000 : ℝ)
                                                                                    hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                    (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                    (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                    hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                    (by constructor <;> norm_num)
                                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                                    (by norm_num) hbudget
                                                                                ·
                                                                                  by_cases h40 : s ≤ (3772981 / 1600000 : ℝ)
                                                                                  ·
                                                                                    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                      (94277 / 40000 : ℝ) (3772981 / 1600000 : ℝ) (56291901 / 25000000 : ℝ)
                                                                                      (28609883 / 50000000 : ℝ) (13897681 / 25000000 : ℝ)
                                                                                      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                      hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                      (by constructor <;> norm_num)
                                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                                      (by norm_num) hbudget
                                                                                  ·
                                                                                    by_cases h41 : s ≤ (1887441 / 800000 : ℝ)
                                                                                    ·
                                                                                      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                        (3772981 / 1600000 : ℝ) (1887441 / 800000 : ℝ) (225034681 / 100000000 : ℝ)
                                                                                        (11447139 / 20000000 : ℝ) (13891799 / 25000000 : ℝ)
                                                                                        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                        hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                        (by constructor <;> norm_num)
                                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                                        (by norm_num) hbudget
                                                                                    ·
                                                                                      by_cases h42 : s ≤ (3776783 / 1600000 : ℝ)
                                                                                      ·
                                                                                        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                          (1887441 / 800000 : ℝ) (3776783 / 1600000 : ℝ) (224902131 / 100000000 : ℝ)
                                                                                          (57251573 / 100000000 : ℝ) (11108731 / 20000000 : ℝ)
                                                                                          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                          hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                          (by constructor <;> norm_num)
                                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                                          (by norm_num) hbudget
                                                                                      ·
                                                                                        by_cases h43 : s ≤ (944671 / 400000 : ℝ)
                                                                                        ·
                                                                                          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                            (3776783 / 1600000 : ℝ) (944671 / 400000 : ℝ) (112384977 / 50000000 : ℝ)
                                                                                            (57267399 / 100000000 : ℝ) (27760051 / 50000000 : ℝ)
                                                                                            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                            hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                            (by constructor <;> norm_num)
                                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                                            (by norm_num) hbudget
                                                                                        ·
                                                                                          by_cases h44 : s ≤ (756117 / 320000 : ℝ)
                                                                                          ·
                                                                                            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                              (944671 / 400000 : ℝ) (756117 / 320000 : ℝ) (4492763 / 2000000 : ℝ)
                                                                                              (28641587 / 50000000 : ℝ) (55496537 / 100000000 : ℝ)
                                                                                              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                              hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                              (by constructor <;> norm_num)
                                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                                              (by norm_num) hbudget
                                                                                          ·
                                                                                            by_cases h45 : s ≤ (1891243 / 800000 : ℝ)
                                                                                            ·
                                                                                              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                (756117 / 320000 : ℝ) (1891243 / 800000 : ℝ) (224506719 / 100000000 : ℝ)
                                                                                                (28649449 / 50000000 : ℝ) (55472961 / 100000000 : ℝ)
                                                                                                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                (by constructor <;> norm_num)
                                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                                (by norm_num) hbudget
                                                                                            ·
                                                                                              by_cases h46 : s ≤ (3784387 / 1600000 : ℝ)
                                                                                              ·
                                                                                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                  (1891243 / 800000 : ℝ) (3784387 / 1600000 : ℝ) (11218783 / 5000000 : ℝ)
                                                                                                  (57314571 / 100000000 : ℝ) (27724687 / 50000000 : ℝ)
                                                                                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                  (by constructor <;> norm_num)
                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                  (by norm_num) hbudget
                                                                                              ·
                                                                                                by_cases h47 : s ≤ (236643 / 100000 : ℝ)
                                                                                                ·
                                                                                                  exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                    (3784387 / 1600000 : ℝ) (236643 / 100000 : ℝ) (112122487 / 50000000 : ℝ)
                                                                                                    (57330193 / 100000000 : ℝ) (3464111 / 6250000 : ℝ)
                                                                                                    hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                    (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                    (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                    hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                    (by constructor <;> norm_num)
                                                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                                                    (by norm_num) hbudget
                                                                                                ·
                                                                                                  by_cases h48 : s ≤ (3788189 / 1600000 : ℝ)
                                                                                                  ·
                                                                                                    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                      (236643 / 100000 : ℝ) (3788189 / 1600000 : ℝ) (11205733 / 5000000 : ℝ)
                                                                                                      (11469153 / 20000000 : ℝ) (6925271 / 12500000 : ℝ)
                                                                                                      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                      hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                      (by constructor <;> norm_num)
                                                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                                                      (by norm_num) hbudget
                                                                                                  ·
                                                                                                    by_cases h49 : s ≤ (379009 / 160000 : ℝ)
                                                                                                    ·
                                                                                                      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                        (3788189 / 1600000 : ℝ) (379009 / 160000 : ℝ) (223984719 / 100000000 : ℝ)
                                                                                                        (28680643 / 50000000 : ℝ) (55378551 / 100000000 : ℝ)
                                                                                                        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                        hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                        (by constructor <;> norm_num)
                                                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                                                        (by norm_num) hbudget
                                                                                                    ·
                                                                                                      by_cases h50 : s ≤ (3791991 / 1600000 : ℝ)
                                                                                                      ·
                                                                                                        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                          (379009 / 160000 : ℝ) (3791991 / 1600000 : ℝ) (4477103 / 2000000 : ℝ)
                                                                                                          (14344189 / 25000000 : ℝ) (13838731 / 25000000 : ℝ)
                                                                                                          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                          hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                          (by constructor <;> norm_num)
                                                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                                                          (by norm_num) hbudget
                                                                                                      ·
                                                                                                        by_cases h51 : s ≤ (948473 / 400000 : ℝ)
                                                                                                        ·
                                                                                                          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                            (3791991 / 1600000 : ℝ) (948473 / 400000 : ℝ) (223725953 / 100000000 : ℝ)
                                                                                                            (57392177 / 100000000 : ℝ) (55331289 / 100000000 : ℝ)
                                                                                                            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                            hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                            (by constructor <;> norm_num)
                                                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                                                            (by norm_num) hbudget
                                                                                                        ·
                                                                                                          by_cases h52 : s ≤ (3795793 / 1600000 : ℝ)
                                                                                                          ·
                                                                                                            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                              (948473 / 400000 : ℝ) (3795793 / 1600000 : ℝ) (223597127 / 100000000 : ℝ)
                                                                                                              (57407547 / 100000000 : ℝ) (11061529 / 20000000 : ℝ)
                                                                                                              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                              hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                              (by constructor <;> norm_num)
                                                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                                                              (by norm_num) hbudget
                                                                                                          ·
                                                                                                            by_cases h53 : s ≤ (1898847 / 800000 : ℝ)
                                                                                                            ·
                                                                                                              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                (3795793 / 1600000 : ℝ) (1898847 / 800000 : ℝ) (111734337 / 50000000 : ℝ)
                                                                                                                (28711433 / 50000000 : ℝ) (55283993 / 100000000 : ℝ)
                                                                                                                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                (by constructor <;> norm_num)
                                                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                                                (by norm_num) hbudget
                                                                                                            ·
                                                                                                              by_cases h54 : s ≤ (759919 / 320000 : ℝ)
                                                                                                              ·
                                                                                                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                  (1898847 / 800000 : ℝ) (759919 / 320000 : ℝ) (13958787 / 6250000 : ℝ)
                                                                                                                  (7179767 / 12500000 : ℝ) (27630167 / 50000000 : ℝ)
                                                                                                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                  (by constructor <;> norm_num)
                                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                                  (by norm_num) hbudget
                                                                                                              ·
                                                                                                                by_cases h55 : s ≤ (475187 / 200000 : ℝ)
                                                                                                                ·
                                                                                                                  exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                    (759919 / 320000 : ℝ) (475187 / 200000 : ℝ) (111606441 / 50000000 : ℝ)
                                                                                                                    (14363339 / 25000000 : ℝ) (13809167 / 25000000 : ℝ)
                                                                                                                    hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                    (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                    (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                    hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                    (by constructor <;> norm_num)
                                                                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                                                                    (by norm_num [contactCos, sinCubicUpper])
                                                                                                                    (by norm_num) hbudget
                                                                                                                ·
                                                                                                                  by_cases h56 : s ≤ (3803397 / 1600000 : ℝ)
                                                                                                                  ·
                                                                                                                    exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                      (475187 / 200000 : ℝ) (3803397 / 1600000 : ℝ) (223085543 / 100000000 : ℝ)
                                                                                                                      (28734263 / 50000000 : ℝ) (11042599 / 20000000 : ℝ)
                                                                                                                      hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                      (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                      (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                      hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                      (by constructor <;> norm_num)
                                                                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                                                                      (by norm_num [contactCos, sinCubicUpper])
                                                                                                                      (by norm_num) hbudget
                                                                                                                  ·
                                                                                                                    by_cases h57 : s ≤ (1902649 / 800000 : ℝ)
                                                                                                                    ·
                                                                                                                      exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                        (3803397 / 1600000 : ℝ) (1902649 / 800000 : ℝ) (13934911 / 6250000 : ℝ)
                                                                                                                        (28741823 / 50000000 : ℝ) (13797329 / 25000000 : ℝ)
                                                                                                                        hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                        (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                        (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                        hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                        (by constructor <;> norm_num)
                                                                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                                                                        (by norm_num [contactCos, sinCubicUpper])
                                                                                                                        (by norm_num) hbudget
                                                                                                                    ·
                                                                                                                      by_cases h58 : s ≤ (3807199 / 1600000 : ℝ)
                                                                                                                      ·
                                                                                                                        exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                          (1902649 / 800000 : ℝ) (3807199 / 1600000 : ℝ) (11141599 / 5000000 : ℝ)
                                                                                                                          (57498717 / 100000000 : ℝ) (55165631 / 100000000 : ℝ)
                                                                                                                          hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                          (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                          (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                          hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                          (by constructor <;> norm_num)
                                                                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                                                                          (by norm_num [contactCos, sinCubicUpper])
                                                                                                                          (by norm_num) hbudget
                                                                                                                      ·
                                                                                                                        by_cases h59 : s ≤ (38091 / 16000 : ℝ)
                                                                                                                        ·
                                                                                                                          exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                            (3807199 / 1600000 : ℝ) (38091 / 16000 : ℝ) (111352877 / 50000000 : ℝ)
                                                                                                                            (28756869 / 50000000 : ℝ) (55141941 / 100000000 : ℝ)
                                                                                                                            hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                            (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                            (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                            hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                            (by constructor <;> norm_num)
                                                                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                                                                            (by norm_num [contactCos, sinCubicUpper])
                                                                                                                            (by norm_num) hbudget
                                                                                                                        ·
                                                                                                                          by_cases h60 : s ≤ (3811001 / 1600000 : ℝ)
                                                                                                                          ·
                                                                                                                            exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                              (38091 / 16000 : ℝ) (3811001 / 1600000 : ℝ) (2225799 / 1000000 : ℝ)
                                                                                                                              (5752871 / 10000000 : ℝ) (27559123 / 50000000 : ℝ)
                                                                                                                              hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                              (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                              (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                              hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                              (by constructor <;> norm_num)
                                                                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                                                                              (by norm_num [contactCos, sinCubicUpper])
                                                                                                                              (by norm_num) hbudget
                                                                                                                          ·
                                                                                                                            by_cases h61 : s ≤ (1906451 / 800000 : ℝ)
                                                                                                                            ·
                                                                                                                              exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                                (3811001 / 1600000 : ℝ) (1906451 / 800000 : ℝ) (222454417 / 100000000 : ℝ)
                                                                                                                                (3596477 / 6250000 : ℝ) (27547273 / 50000000 : ℝ)
                                                                                                                                hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                                (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                                (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                                hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                                (by constructor <;> norm_num)
                                                                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                                                                (by norm_num [contactCos, sinCubicUpper])
                                                                                                                                (by norm_num) hbudget
                                                                                                                            ·
                                                                                                                              by_cases h62 : s ≤ (3814803 / 1600000 : ℝ)
                                                                                                                              ·
                                                                                                                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                                  (1906451 / 800000 : ℝ) (3814803 / 1600000 : ℝ) (27791163 / 12500000 : ℝ)
                                                                                                                                  (11511701 / 20000000 : ℝ) (55070843 / 100000000 : ℝ)
                                                                                                                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                                  (by constructor <;> norm_num)
                                                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                                                  (by norm_num) hbudget
                                                                                                                              ·
                                                                                                                                exact k9_scalar_bin_contradiction b s z r δ₁ δ₂
                                                                                                                                  (3814803 / 1600000 : ℝ) (14909 / 6250 : ℝ) (222204561 / 100000000 : ℝ)
                                                                                                                                  (57573329 / 100000000 : ℝ) (11009427 / 20000000 : ℝ)
                                                                                                                                  hb3 hbB hb12 hs2 (by norm_num) (by linarith) (by linarith)
                                                                                                                                  (by norm_num) (by norm_num) hz2 hzhi hrlower hzsq
                                                                                                                                  (by norm_num) (by norm_num) hδ₁0 hδ₁pi hδ₂0 hδ₂pi
                                                                                                                                  hlaw₁ hlaw₂ (by constructor <;> norm_num)
                                                                                                                                  (by constructor <;> norm_num)
                                                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                                                  (by norm_num [contactCos, sinCubicUpper])
                                                                                                                                  (by norm_num) hbudget

end CP15
