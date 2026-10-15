import CP15.RationalFullAngle

namespace CP15

set_option maxHeartbeats 0

theorem cos_taylor_ten_lower (x : ℝ) (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800)
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hh := sin_taylor_nine_upper t ht'.le
    have hd : deriv f t = (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880) - Real.sin t := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at hh
  exact sub_nonneg.mp hh

theorem sin_taylor_eleven_lower (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 ≤ Real.sin x := by
  let f : ℝ → ℝ := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800)
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hh := cos_taylor_ten_lower t ht'.le
    have hd : deriv f t = Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800) := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at hh
  exact sub_nonneg.mp hh

theorem cos_taylor_twelve_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600 := by
  let f : ℝ → ℝ := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600) - Real.cos t
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hh := sin_taylor_eleven_lower t ht'.le
    have hd : deriv f t = Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800) := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at hh
  exact sub_nonneg.mp hh

theorem sin_taylor_thirteen_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 + x ^ 13 / 6227020800 := by
  let f : ℝ → ℝ := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800) - Real.sin t
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hh := cos_taylor_twelve_upper t ht'.le
    have hd : deriv f t = (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600) - Real.cos t := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at hh
  exact sub_nonneg.mp hh

theorem cos_taylor_fourteen_lower (x : ℝ) (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200)
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hh := sin_taylor_thirteen_upper t ht'.le
    have hd : deriv f t = (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800) - Real.sin t := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at hh
  exact sub_nonneg.mp hh

end CP15
