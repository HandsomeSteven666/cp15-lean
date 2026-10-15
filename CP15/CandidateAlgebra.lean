import CP15.Global

namespace CP15.Candidate

noncomputable def root5 : ℝ := Real.sqrt 5
noncomputable def s : ℝ := Real.sqrt (10 - 2 * root5) / 4
noncomputable def c : ℝ := (1 + root5) / 4
noncomputable def u : ℝ := Real.sqrt (10 + 2 * root5) / 4
noncomputable def v : ℝ := (root5 - 1) / 4
noncomputable def t : ℝ := 1 / (2 * s)
noncomputable def rho : ℝ := Real.sqrt (s ^ 2 + (t + c) ^ 2)

theorem root5_sq : root5 ^ 2 = 5 := by
  unfold root5
  exact Real.sq_sqrt (by norm_num)

theorem root5_bounds : 2 < root5 ∧ root5 < 3 := by
  have hs := root5_sq
  have hnonneg : 0 ≤ root5 := Real.sqrt_nonneg _
  constructor <;> nlinarith

theorem root5_tight_bounds : (223 / 100 : ℝ) < root5 ∧
    root5 < 9 / 4 := by
  have hs := root5_sq
  have hnonneg : 0 ≤ root5 := Real.sqrt_nonneg _
  constructor <;> nlinarith

theorem s_sq : s ^ 2 = (5 - root5) / 8 := by
  have hrad : 0 ≤ 10 - 2 * root5 := by
    have h := root5_bounds.2
    linarith
  unfold s
  rw [div_pow, Real.sq_sqrt hrad]
  ring

theorem u_sq : u ^ 2 = (5 + root5) / 8 := by
  have hrad : 0 ≤ 10 + 2 * root5 := by
    have h := root5_bounds.1
    linarith
  unfold u
  rw [div_pow, Real.sq_sqrt hrad]
  ring

theorem c_sq : c ^ 2 = (3 + root5) / 8 := by
  have h := root5_sq
  unfold c
  ring_nf
  nlinarith

theorem v_sq : v ^ 2 = (3 - root5) / 8 := by
  have h := root5_sq
  unfold v
  ring_nf
  nlinarith

theorem s_pos : 0 < s := by
  have h := s_sq
  have h5 := root5_bounds.2
  have hsnonneg : 0 ≤ s := by
    unfold s
    positivity
  nlinarith

theorem u_pos : 0 < u := by
  have h := u_sq
  have h5 := root5_bounds.1
  have hunonneg : 0 ≤ u := by
    unfold u
    positivity
  nlinarith

theorem simple_bounds :
    (29 / 50 : ℝ) < s ∧ s < 3 / 5 ∧
    (4 / 5 : ℝ) < c ∧ c < 13 / 16 ∧
    (19 / 20 : ℝ) < u ∧ u < 24 / 25 ∧
    (3 / 10 : ℝ) < v ∧ v < 8 / 25 := by
  have hs := s_sq
  have hc := c_sq
  have hu := u_sq
  have hv := v_sq
  have h5lo := root5_tight_bounds.1
  have h5hi := root5_tight_bounds.2
  have hs0 := s_pos
  have hu0 := u_pos
  have hc0 : 0 < c := by
    unfold c
    have h := root5_bounds.1
    positivity
  have hv0 : 0 < v := by
    unfold v
    linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · unfold c
    linarith
  constructor
  · unfold c
    linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · unfold v
    linarith
  · unfold v
    linarith

theorem t_pos : 0 < t := by
  unfold t
  positivity [s_pos]

theorem pentagon_identity : s ^ 2 + c ^ 2 = 1 := by
  rw [s_sq, c_sq]
  ring

theorem square_identity : u ^ 2 + v ^ 2 = 1 := by
  rw [u_sq, v_sq]
  ring

theorem c_pos : 0 < c := by
  unfold c
  have h := root5_bounds.1
  positivity

theorem v_pos : 0 < v := by
  unfold v
  have h := root5_bounds.1
  linarith

theorem v_lt_half : v < 1 / 2 := by
  unfold v
  have h := root5_bounds.2
  linarith

theorem two_s_sq : 2 * s ^ 2 = 1 - v := by
  rw [s_sq]
  unfold v
  ring

theorem two_c_sq : 2 * c ^ 2 = 1 + v := by
  rw [c_sq]
  unfold v
  ring

theorem two_s_c : 2 * s * c = u := by
  have hsq : (2 * s * c) ^ 2 = u ^ 2 := by
    calc
      (2 * s * c) ^ 2 = 4 * s ^ 2 * c ^ 2 := by ring
      _ = u ^ 2 := by
        rw [s_sq, c_sq, u_sq]
        nlinarith [root5_sq]
  have hpos : 0 ≤ 2 * s * c := by positivity [s_pos, c_pos]
  nlinarith [u_pos]

theorem two_u_v : 2 * u * v = s := by
  have hsq : (2 * u * v) ^ 2 = s ^ 2 := by
    calc
      (2 * u * v) ^ 2 = 4 * u ^ 2 * v ^ 2 := by ring
      _ = s ^ 2 := by
        rw [u_sq, v_sq, s_sq]
        nlinarith [root5_sq]
  have hpos : 0 ≤ 2 * u * v := by positivity [u_pos, v_pos]
  nlinarith [s_pos]

theorem s_mul_u : s * u = root5 / 4 := by
  have hsq : (s * u) ^ 2 = (root5 / 4) ^ 2 := by
    rw [mul_pow, s_sq, u_sq]
    nlinarith [root5_sq]
  have hpos : 0 ≤ s * u := by positivity [s_pos, u_pos]
  have hrpos : 0 ≤ root5 / 4 := by
    have h := root5_bounds.1
    positivity
  nlinarith

theorem t_linear : t = (4 * s + 2 * u) / 5 := by
  unfold t
  have hsne : s ≠ 0 := ne_of_gt s_pos
  field_simp
  nlinarith [s_sq, s_mul_u]

theorem c_sub_v : c - v = 1 / 2 := by
  unfold c v
  ring

theorem u_sq_v : 4 * u ^ 2 = 3 + 2 * v := by
  rw [u_sq]
  unfold v
  ring

theorem v_sq_v : 4 * v ^ 2 + 2 * v = 1 := by
  rw [v_sq]
  unfold v
  ring

theorem s_u_v : s * u = v + 1 / 4 := by
  rw [s_mul_u]
  unfold v
  ring

theorem two_s_v : 2 * s * v = u - s := by
  have hv : v = c - 1 / 2 := by linarith [c_sub_v]
  rw [hv]
  nlinarith [two_s_c]

theorem two_c_u : 2 * c * u = s + u := by
  have hc : c = v + 1 / 2 := by linarith [c_sub_v]
  rw [hc]
  nlinarith [two_u_v]

theorem four_c_v : 4 * c * v = 1 := by
  have hc : c = v + 1 / 2 := by linarith [c_sub_v]
  rw [hc]
  nlinarith [v_sq_v]

theorem root5_pos : 0 < root5 := (by norm_num : (0 : ℝ) < 2).trans root5_bounds.1

theorem inv_s_sq : 1 / s ^ 2 = 2 + 2 / root5 := by
  have hsne : s ≠ 0 := ne_of_gt s_pos
  have hrne : root5 ≠ 0 := ne_of_gt root5_pos
  have h5 := root5_sq
  rw [s_sq]
  have hden : 5 - root5 ≠ 0 := by
    have h := root5_bounds.2
    linarith
  field_simp
  nlinarith

theorem c_div_s_sq : (c / s) ^ 2 = 1 + 2 / root5 := by
  have hsne : s ≠ 0 := ne_of_gt s_pos
  have hrne : root5 ≠ 0 := ne_of_gt root5_pos
  have h5 := root5_sq
  rw [div_pow, c_sq, s_sq]
  have hden : 5 - root5 ≠ 0 := by
    have h := root5_bounds.2
    linarith
  field_simp
  nlinarith

theorem c_div_s_eq_sqrt :
    c / s = Real.sqrt (1 + 2 / root5) := by
  have hrad : 0 ≤ 1 + 2 / root5 := by positivity [root5_pos]
  have hsq := c_div_s_sq
  have hpos : 0 ≤ c / s := by positivity [c_pos, s_pos]
  nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 + 2 / root5)]

theorem rho_sq : rho ^ 2 = s ^ 2 + (t + c) ^ 2 := by
  unfold rho
  rw [Real.sq_sqrt]
  positivity [s_pos]

theorem two_rho_sq :
    (2 * rho) ^ 2 =
      6 + 2 / root5 + 4 * Real.sqrt (1 + 2 / root5) := by
  have hsne : s ≠ 0 := ne_of_gt s_pos
  have htsq : t ^ 2 = 1 / (4 * s ^ 2) := by
    unfold t
    ring
  have htc : t * c = c / (2 * s) := by
    unfold t
    ring
  calc
    (2 * rho) ^ 2 = 4 * rho ^ 2 := by ring
    _ = 4 * (s ^ 2 + (t + c) ^ 2) := by rw [rho_sq]
    _ = 4 * (s ^ 2 + c ^ 2) + 4 * t ^ 2 + 8 * (t * c) := by ring
    _ = 4 + 1 / s ^ 2 + 4 * (c / s) := by
      rw [pentagon_identity, htsq, htc]
      field_simp
      ring
    _ = 6 + 2 / root5 + 4 * Real.sqrt (1 + 2 / root5) := by
      rw [inv_s_sq, c_div_s_eq_sqrt]
      ring

theorem two_rho_eq_candidateB : 2 * rho = CP15.candidateB := by
  have hrad : 0 ≤ 1 + 2 / root5 := by positivity [root5_pos]
  have hBsq : CP15.candidateB ^ 2 =
      6 + 2 / root5 + 4 * Real.sqrt (1 + 2 / root5) := by
    unfold CP15.candidateB root5
    rw [Real.sq_sqrt]
    positivity
  have hrho : 0 ≤ rho := by
    unfold rho
    exact Real.sqrt_nonneg _
  have hB : 0 ≤ CP15.candidateB := CP15.candidateB_pos.le
  nlinarith [two_rho_sq]

end CP15.Candidate
