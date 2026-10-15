import CP15.Definitions

namespace CP15

/-- Alternating polynomial bounds are proved by derivative comparisons
starting with the library's global cubic sine lower bound. No sampled
values, floating-point remainder, or externally asserted Taylor sign is
used. -/
theorem cos_taylor_four_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24)
  have hd (t : ℝ) : deriv f t = -Real.sin t + t - t ^ 3 / 6 := by
    simp (disch := fun_prop) [f]
    ring
  have hm : AntitoneOn f (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have ht0 : 0 ≤ t := ht'.le
    rw [hd]
    linarith [Real.sin_ge_sub_cube ht0]
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at h
  exact sub_nonpos.mp h

theorem sin_taylor_five_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hd (t : ℝ) : deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have ht0 : 0 ≤ t := ht'.le
    rw [hd]
    linarith [cos_taylor_four_upper t ht0]
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at h
  exact sub_nonneg.mp h

theorem cos_taylor_six_lower (x : ℝ) (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hd (t : ℝ) : deriv f t = t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have ht0 : 0 ≤ t := ht'.le
    rw [hd]
    linarith [sin_taylor_five_upper t ht0]
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at h
  exact sub_nonneg.mp h

theorem sin_taylor_seven_lower (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  let f : ℝ → ℝ := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hd (t : ℝ) : deriv f t = Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have ht0 : 0 ≤ t := ht'.le
    rw [hd]
    linarith [cos_taylor_six_lower t ht0]
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at h
  exact sub_nonneg.mp h

end CP15
