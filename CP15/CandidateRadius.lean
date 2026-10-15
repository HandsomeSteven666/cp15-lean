import CP15.CandidateGeometry

set_option maxHeartbeats 2000000

namespace CP15.Candidate

theorem radius_sq_00 : ‖point 0‖ ^ 2 = rho ^ 2 := by
  rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (-1) * pentagon_identity + (-4/5) * two_s_c + (-3/10) * two_s_sq + (-2/5) * s_u_v + (-2/5) * two_c_u + (1/20) * u_sq_v

theorem radius_sq_01 : ‖point 1‖ ^ 2 = rho ^ 2 := by
  rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (-1) * pentagon_identity + (-4/5) * two_s_c + (-3/10) * two_s_sq + (-2/5) * s_u_v + (-2/5) * two_c_u + (1/20) * u_sq_v

theorem radius_sq_02 : ‖point 2‖ ^ 2 = rho ^ 2 := by
  rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (-1) * pentagon_identity + (1) * square_identity + (-4/5) * two_s_c + (3/5) * two_u_v + (-3/10) * two_s_sq + (-2/5) * s_u_v + (1/5) * two_s_v + (-2/5) * two_c_u + (1/20) * u_sq_v

theorem radius_sq_03 : ‖point 3‖ ^ 2 = rho ^ 2 := by
  rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (-1) * pentagon_identity + (1) * square_identity + (-4/5) * two_s_c + (3/5) * two_u_v + (-3/10) * two_s_sq + (-2/5) * s_u_v + (1/5) * two_s_v + (-2/5) * two_c_u + (1/20) * u_sq_v

theorem radius_sq_04 : ‖point 4‖ ^ 2 = t ^ 2 := by
  rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, norm_pt_sq, t_linear]
  linear_combination (-3/10) * two_s_sq + (-2/5) * s_u_v + (1/20) * u_sq_v

theorem radius_sq_05 : ‖point 5‖ ^ 2 = t ^ 2 := by
  rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, norm_pt_sq, t_linear]
  linear_combination (-3/10) * two_s_sq + (-2/5) * s_u_v + (1/20) * u_sq_v

theorem radius_sq_06 : ‖point 6‖ ^ 2 = rho ^ 2 := by
  rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (-1) * pentagon_identity + (2) * square_identity + (-4/5) * two_s_c + (3/5) * two_u_v + (-3/10) * two_s_sq + (-4/5) * s_u_v + (1/5) * two_s_v + (-2/5) * two_c_u + (-1/4) * u_sq_v

theorem radius_sq_07 : ‖point 7‖ ^ 2 = rho ^ 2 := by
  rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (-1) * pentagon_identity + (2) * square_identity + (-4/5) * two_s_c + (3/5) * two_u_v + (-3/10) * two_s_sq + (-4/5) * s_u_v + (1/5) * two_s_v + (-2/5) * two_c_u + (-1/4) * u_sq_v

theorem radius_sq_08 : ‖point 8‖ ^ 2 = t ^ 2 := by
  rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl, norm_pt_sq, t_linear]
  linear_combination (1) * pentagon_identity + (-4/5) * two_s_sq + (-4/5) * s_u_v

theorem radius_sq_09 : ‖point 9‖ ^ 2 = t ^ 2 := by
  rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl, norm_pt_sq, t_linear]
  linear_combination (1) * pentagon_identity + (-4/5) * two_s_sq + (-4/5) * s_u_v

theorem radius_sq_10 : ‖point 10‖ ^ 2 = t ^ 2 := by
  rw [show point (10 : Fin 15) = pt (0) (t) by rfl, norm_pt_sq, t_linear]
  ring

theorem radius_sq_11 : ‖point 11‖ ^ 2 = rho ^ 2 := by
  rw [show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (1) * pentagon_identity + (-4/5) * two_s_sq + (-4/5) * s_u_v

theorem radius_sq_12 : ‖point 12‖ ^ 2 = rho ^ 2 := by
  rw [show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, norm_pt_sq, rho_sq, t_linear]
  linear_combination (1) * pentagon_identity + (-4/5) * two_s_sq + (-4/5) * s_u_v

theorem radius_sq_13 : ‖point 13‖ ^ 2 = rho ^ 2 := by
  rw [show point (13 : Fin 15) = pt (-s) (t + c) by rfl, norm_pt_sq, rho_sq, t_linear]
  ring

theorem radius_sq_14 : ‖point 14‖ ^ 2 = rho ^ 2 := by
  rw [show point (14 : Fin 15) = pt (s) (t + c) by rfl, norm_pt_sq, rho_sq, t_linear]
  

theorem inner_radius_lt : t ^ 2 < rho ^ 2 := by
  rw [rho_sq]
  nlinarith [pentagon_identity, mul_pos t_pos c_pos, sq_pos_of_pos s_pos]

theorem all_radius_le (i : Fin 15) : ‖point i‖ ≤ rho := by
  have hrho : 0 ≤ rho := by unfold rho; positivity
  have hsquare : ‖point i‖ ^ 2 ≤ rho ^ 2 := by
    fin_cases i
    · exact le_of_eq radius_sq_00
    · exact le_of_eq radius_sq_01
    · exact le_of_eq radius_sq_02
    · exact le_of_eq radius_sq_03
    · exact le_of_lt (radius_sq_04.trans_lt inner_radius_lt)
    · exact le_of_lt (radius_sq_05.trans_lt inner_radius_lt)
    · exact le_of_eq radius_sq_06
    · exact le_of_eq radius_sq_07
    · exact le_of_lt (radius_sq_08.trans_lt inner_radius_lt)
    · exact le_of_lt (radius_sq_09.trans_lt inner_radius_lt)
    · exact le_of_lt (radius_sq_10.trans_lt inner_radius_lt)
    · exact le_of_eq radius_sq_11
    · exact le_of_eq radius_sq_12
    · exact le_of_eq radius_sq_13
    · exact le_of_eq radius_sq_14
  nlinarith [norm_nonneg (point i)]

end CP15.Candidate
