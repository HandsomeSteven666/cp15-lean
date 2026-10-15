import CP15.CandidateGeometry

set_option maxHeartbeats 2000000

namespace CP15.Candidate

theorem pair_00_01 : 1 ≤ dist (point 0) (point 1) := by
  have hsq : 1 ≤ dist (point 0) (point 1) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 1) := dist_nonneg
  nlinarith

theorem pair_00_02 : 1 ≤ dist (point 0) (point 2) := by
  have hsq : 1 ≤ dist (point 0) (point 2) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 2) := dist_nonneg
  nlinarith

theorem pair_00_03 : 1 ≤ dist (point 0) (point 3) := by
  have hsq : 1 ≤ dist (point 0) (point 3) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 3) := dist_nonneg
  nlinarith

theorem pair_00_04 : 1 ≤ dist (point 0) (point 4) := by
  have hsq : 1 ≤ dist (point 0) (point 4) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 4) := dist_nonneg
  nlinarith

theorem pair_00_05 : 1 ≤ dist (point 0) (point 5) := by
  have hsq : 1 ≤ dist (point 0) (point 5) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 5) := dist_nonneg
  nlinarith

theorem pair_00_06 : 1 ≤ dist (point 0) (point 6) := by
  have hsq : 1 ≤ dist (point 0) (point 6) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 6) := dist_nonneg
  nlinarith

theorem pair_00_07 : 1 ≤ dist (point 0) (point 7) := by
  have hsq : 1 ≤ dist (point 0) (point 7) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 7) := dist_nonneg
  nlinarith

theorem pair_00_08 : 1 ≤ dist (point 0) (point 8) := by
  have hsq : 1 ≤ dist (point 0) (point 8) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 8) := dist_nonneg
  nlinarith

theorem pair_00_09 : 1 ≤ dist (point 0) (point 9) := by
  have hsq : 1 ≤ dist (point 0) (point 9) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 9) := dist_nonneg
  nlinarith

theorem pair_00_10 : 1 ≤ dist (point 0) (point 10) := by
  have hsq : 1 ≤ dist (point 0) (point 10) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 10) := dist_nonneg
  nlinarith

theorem pair_00_11 : 1 ≤ dist (point 0) (point 11) := by
  have hsq : 1 ≤ dist (point 0) (point 11) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 11) := dist_nonneg
  nlinarith

theorem pair_00_12 : 1 ≤ dist (point 0) (point 12) := by
  have hsq : 1 ≤ dist (point 0) (point 12) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 12) := dist_nonneg
  nlinarith

theorem pair_00_13 : 1 ≤ dist (point 0) (point 13) := by
  have hsq : 1 ≤ dist (point 0) (point 13) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 13) := dist_nonneg
  nlinarith

theorem pair_00_14 : 1 ≤ dist (point 0) (point 14) := by
  have hsq : 1 ≤ dist (point 0) (point 14) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 14) := dist_nonneg
  nlinarith

theorem pair_01_02 : 1 ≤ dist (point 1) (point 2) := by
  have hsq : 1 ≤ dist (point 1) (point 2) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 2) := dist_nonneg
  nlinarith

theorem pair_01_03 : 1 ≤ dist (point 1) (point 3) := by
  have hsq : 1 ≤ dist (point 1) (point 3) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 3) := dist_nonneg
  nlinarith

theorem pair_01_04 : 1 ≤ dist (point 1) (point 4) := by
  have hsq : 1 ≤ dist (point 1) (point 4) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 4) := dist_nonneg
  nlinarith

theorem pair_01_05 : 1 ≤ dist (point 1) (point 5) := by
  have hsq : 1 ≤ dist (point 1) (point 5) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 5) := dist_nonneg
  nlinarith

theorem pair_01_06 : 1 ≤ dist (point 1) (point 6) := by
  have hsq : 1 ≤ dist (point 1) (point 6) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 6) := dist_nonneg
  nlinarith

theorem pair_01_07 : 1 ≤ dist (point 1) (point 7) := by
  have hsq : 1 ≤ dist (point 1) (point 7) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 7) := dist_nonneg
  nlinarith

theorem pair_01_08 : 1 ≤ dist (point 1) (point 8) := by
  have hsq : 1 ≤ dist (point 1) (point 8) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 8) := dist_nonneg
  nlinarith

theorem pair_01_09 : 1 ≤ dist (point 1) (point 9) := by
  have hsq : 1 ≤ dist (point 1) (point 9) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 9) := dist_nonneg
  nlinarith

theorem pair_01_10 : 1 ≤ dist (point 1) (point 10) := by
  have hsq : 1 ≤ dist (point 1) (point 10) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 10) := dist_nonneg
  nlinarith

theorem pair_01_11 : 1 ≤ dist (point 1) (point 11) := by
  have hsq : 1 ≤ dist (point 1) (point 11) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 11) := dist_nonneg
  nlinarith

theorem pair_01_12 : 1 ≤ dist (point 1) (point 12) := by
  have hsq : 1 ≤ dist (point 1) (point 12) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 12) := dist_nonneg
  nlinarith

theorem pair_01_13 : 1 ≤ dist (point 1) (point 13) := by
  have hsq : 1 ≤ dist (point 1) (point 13) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 13) := dist_nonneg
  nlinarith

theorem pair_01_14 : 1 ≤ dist (point 1) (point 14) := by
  have hsq : 1 ≤ dist (point 1) (point 14) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 14) := dist_nonneg
  nlinarith

theorem pair_02_03 : 1 ≤ dist (point 2) (point 3) := by
  have hsq : 1 ≤ dist (point 2) (point 3) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 3) := dist_nonneg
  nlinarith

theorem pair_02_04 : 1 ≤ dist (point 2) (point 4) := by
  have hsq : 1 ≤ dist (point 2) (point 4) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 4) := dist_nonneg
  nlinarith

theorem pair_02_05 : 1 ≤ dist (point 2) (point 5) := by
  have hsq : 1 ≤ dist (point 2) (point 5) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 5) := dist_nonneg
  nlinarith

theorem pair_02_06 : 1 ≤ dist (point 2) (point 6) := by
  have hsq : 1 ≤ dist (point 2) (point 6) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 6) := dist_nonneg
  nlinarith

theorem pair_02_07 : 1 ≤ dist (point 2) (point 7) := by
  have hsq : 1 ≤ dist (point 2) (point 7) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 7) := dist_nonneg
  nlinarith

theorem pair_02_08 : 1 ≤ dist (point 2) (point 8) := by
  have hsq : 1 ≤ dist (point 2) (point 8) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 8) := dist_nonneg
  nlinarith

theorem pair_02_09 : 1 ≤ dist (point 2) (point 9) := by
  have hsq : 1 ≤ dist (point 2) (point 9) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 9) := dist_nonneg
  nlinarith

theorem pair_02_10 : 1 ≤ dist (point 2) (point 10) := by
  have hsq : 1 ≤ dist (point 2) (point 10) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 10) := dist_nonneg
  nlinarith

theorem pair_02_11 : 1 ≤ dist (point 2) (point 11) := by
  have hsq : 1 ≤ dist (point 2) (point 11) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 11) := dist_nonneg
  nlinarith

theorem pair_02_12 : 1 ≤ dist (point 2) (point 12) := by
  have hsq : 1 ≤ dist (point 2) (point 12) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 12) := dist_nonneg
  nlinarith

theorem pair_02_13 : 1 ≤ dist (point 2) (point 13) := by
  have hsq : 1 ≤ dist (point 2) (point 13) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 13) := dist_nonneg
  nlinarith

theorem pair_02_14 : 1 ≤ dist (point 2) (point 14) := by
  have hsq : 1 ≤ dist (point 2) (point 14) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 14) := dist_nonneg
  nlinarith

theorem pair_03_04 : 1 ≤ dist (point 3) (point 4) := by
  have hsq : 1 ≤ dist (point 3) (point 4) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 4) := dist_nonneg
  nlinarith

theorem pair_03_05 : 1 ≤ dist (point 3) (point 5) := by
  have hsq : 1 ≤ dist (point 3) (point 5) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 5) := dist_nonneg
  nlinarith

theorem pair_03_06 : 1 ≤ dist (point 3) (point 6) := by
  have hsq : 1 ≤ dist (point 3) (point 6) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 6) := dist_nonneg
  nlinarith

theorem pair_03_07 : 1 ≤ dist (point 3) (point 7) := by
  have hsq : 1 ≤ dist (point 3) (point 7) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 7) := dist_nonneg
  nlinarith

theorem pair_03_08 : 1 ≤ dist (point 3) (point 8) := by
  have hsq : 1 ≤ dist (point 3) (point 8) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 8) := dist_nonneg
  nlinarith

theorem pair_03_09 : 1 ≤ dist (point 3) (point 9) := by
  have hsq : 1 ≤ dist (point 3) (point 9) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 9) := dist_nonneg
  nlinarith

theorem pair_03_10 : 1 ≤ dist (point 3) (point 10) := by
  have hsq : 1 ≤ dist (point 3) (point 10) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 10) := dist_nonneg
  nlinarith

theorem pair_03_11 : 1 ≤ dist (point 3) (point 11) := by
  have hsq : 1 ≤ dist (point 3) (point 11) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 11) := dist_nonneg
  nlinarith

theorem pair_03_12 : 1 ≤ dist (point 3) (point 12) := by
  have hsq : 1 ≤ dist (point 3) (point 12) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 12) := dist_nonneg
  nlinarith

theorem pair_03_13 : 1 ≤ dist (point 3) (point 13) := by
  have hsq : 1 ≤ dist (point 3) (point 13) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 13) := dist_nonneg
  nlinarith

theorem pair_03_14 : 1 ≤ dist (point 3) (point 14) := by
  have hsq : 1 ≤ dist (point 3) (point 14) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 14) := dist_nonneg
  nlinarith

theorem pair_04_05 : 1 ≤ dist (point 4) (point 5) := by
  have hsq : 1 ≤ dist (point 4) (point 5) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 5) := dist_nonneg
  nlinarith

theorem pair_04_06 : 1 ≤ dist (point 4) (point 6) := by
  have hsq : 1 ≤ dist (point 4) (point 6) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 6) := dist_nonneg
  nlinarith

theorem pair_04_07 : 1 ≤ dist (point 4) (point 7) := by
  have hsq : 1 ≤ dist (point 4) (point 7) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 7) := dist_nonneg
  nlinarith

theorem pair_04_08 : 1 ≤ dist (point 4) (point 8) := by
  have hsq : 1 ≤ dist (point 4) (point 8) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 8) := dist_nonneg
  nlinarith

theorem pair_04_09 : 1 ≤ dist (point 4) (point 9) := by
  have hsq : 1 ≤ dist (point 4) (point 9) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 9) := dist_nonneg
  nlinarith

theorem pair_04_10 : 1 ≤ dist (point 4) (point 10) := by
  have hsq : 1 ≤ dist (point 4) (point 10) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 10) := dist_nonneg
  nlinarith

theorem pair_04_11 : 1 ≤ dist (point 4) (point 11) := by
  have hsq : 1 ≤ dist (point 4) (point 11) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 11) := dist_nonneg
  nlinarith

theorem pair_04_12 : 1 ≤ dist (point 4) (point 12) := by
  have hsq : 1 ≤ dist (point 4) (point 12) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 12) := dist_nonneg
  nlinarith

theorem pair_04_13 : 1 ≤ dist (point 4) (point 13) := by
  have hsq : 1 ≤ dist (point 4) (point 13) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 13) := dist_nonneg
  nlinarith

theorem pair_04_14 : 1 ≤ dist (point 4) (point 14) := by
  have hsq : 1 ≤ dist (point 4) (point 14) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 14) := dist_nonneg
  nlinarith

theorem pair_05_06 : 1 ≤ dist (point 5) (point 6) := by
  have hsq : 1 ≤ dist (point 5) (point 6) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 6) := dist_nonneg
  nlinarith

theorem pair_05_07 : 1 ≤ dist (point 5) (point 7) := by
  have hsq : 1 ≤ dist (point 5) (point 7) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 7) := dist_nonneg
  nlinarith

theorem pair_05_08 : 1 ≤ dist (point 5) (point 8) := by
  have hsq : 1 ≤ dist (point 5) (point 8) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 8) := dist_nonneg
  nlinarith

theorem pair_05_09 : 1 ≤ dist (point 5) (point 9) := by
  have hsq : 1 ≤ dist (point 5) (point 9) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 9) := dist_nonneg
  nlinarith

theorem pair_05_10 : 1 ≤ dist (point 5) (point 10) := by
  have hsq : 1 ≤ dist (point 5) (point 10) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 10) := dist_nonneg
  nlinarith

theorem pair_05_11 : 1 ≤ dist (point 5) (point 11) := by
  have hsq : 1 ≤ dist (point 5) (point 11) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 11) := dist_nonneg
  nlinarith

theorem pair_05_12 : 1 ≤ dist (point 5) (point 12) := by
  have hsq : 1 ≤ dist (point 5) (point 12) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 12) := dist_nonneg
  nlinarith

theorem pair_05_13 : 1 ≤ dist (point 5) (point 13) := by
  have hsq : 1 ≤ dist (point 5) (point 13) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 13) := dist_nonneg
  nlinarith

theorem pair_05_14 : 1 ≤ dist (point 5) (point 14) := by
  have hsq : 1 ≤ dist (point 5) (point 14) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 14) := dist_nonneg
  nlinarith

theorem pair_06_07 : 1 ≤ dist (point 6) (point 7) := by
  have hsq : 1 ≤ dist (point 6) (point 7) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 7) := dist_nonneg
  nlinarith

theorem pair_06_08 : 1 ≤ dist (point 6) (point 8) := by
  have hsq : 1 ≤ dist (point 6) (point 8) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 8) := dist_nonneg
  nlinarith

theorem pair_06_09 : 1 ≤ dist (point 6) (point 9) := by
  have hsq : 1 ≤ dist (point 6) (point 9) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 9) := dist_nonneg
  nlinarith

theorem pair_06_10 : 1 ≤ dist (point 6) (point 10) := by
  have hsq : 1 ≤ dist (point 6) (point 10) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 10) := dist_nonneg
  nlinarith

theorem pair_06_11 : 1 ≤ dist (point 6) (point 11) := by
  have hsq : 1 ≤ dist (point 6) (point 11) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 11) := dist_nonneg
  nlinarith

theorem pair_06_12 : 1 ≤ dist (point 6) (point 12) := by
  have hsq : 1 ≤ dist (point 6) (point 12) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 12) := dist_nonneg
  nlinarith

theorem pair_06_13 : 1 ≤ dist (point 6) (point 13) := by
  have hsq : 1 ≤ dist (point 6) (point 13) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 13) := dist_nonneg
  nlinarith

theorem pair_06_14 : 1 ≤ dist (point 6) (point 14) := by
  have hsq : 1 ≤ dist (point 6) (point 14) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 14) := dist_nonneg
  nlinarith

theorem pair_07_08 : 1 ≤ dist (point 7) (point 8) := by
  have hsq : 1 ≤ dist (point 7) (point 8) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 8) := dist_nonneg
  nlinarith

theorem pair_07_09 : 1 ≤ dist (point 7) (point 9) := by
  have hsq : 1 ≤ dist (point 7) (point 9) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 9) := dist_nonneg
  nlinarith

theorem pair_07_10 : 1 ≤ dist (point 7) (point 10) := by
  have hsq : 1 ≤ dist (point 7) (point 10) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 10) := dist_nonneg
  nlinarith

theorem pair_07_11 : 1 ≤ dist (point 7) (point 11) := by
  have hsq : 1 ≤ dist (point 7) (point 11) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 11) := dist_nonneg
  nlinarith

theorem pair_07_12 : 1 ≤ dist (point 7) (point 12) := by
  have hsq : 1 ≤ dist (point 7) (point 12) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 12) := dist_nonneg
  nlinarith

theorem pair_07_13 : 1 ≤ dist (point 7) (point 13) := by
  have hsq : 1 ≤ dist (point 7) (point 13) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 13) := dist_nonneg
  nlinarith

theorem pair_07_14 : 1 ≤ dist (point 7) (point 14) := by
  have hsq : 1 ≤ dist (point 7) (point 14) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 14) := dist_nonneg
  nlinarith

theorem pair_08_09 : 1 ≤ dist (point 8) (point 9) := by
  have hsq : 1 ≤ dist (point 8) (point 9) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 9) := dist_nonneg
  nlinarith

theorem pair_08_10 : 1 ≤ dist (point 8) (point 10) := by
  have hsq : 1 ≤ dist (point 8) (point 10) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 10) := dist_nonneg
  nlinarith

theorem pair_08_11 : 1 ≤ dist (point 8) (point 11) := by
  have hsq : 1 ≤ dist (point 8) (point 11) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 11) := dist_nonneg
  nlinarith

theorem pair_08_12 : 1 ≤ dist (point 8) (point 12) := by
  have hsq : 1 ≤ dist (point 8) (point 12) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 12) := dist_nonneg
  nlinarith

theorem pair_08_13 : 1 ≤ dist (point 8) (point 13) := by
  have hsq : 1 ≤ dist (point 8) (point 13) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 13) := dist_nonneg
  nlinarith

theorem pair_08_14 : 1 ≤ dist (point 8) (point 14) := by
  have hsq : 1 ≤ dist (point 8) (point 14) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 14) := dist_nonneg
  nlinarith

theorem pair_09_10 : 1 ≤ dist (point 9) (point 10) := by
  have hsq : 1 ≤ dist (point 9) (point 10) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 10) := dist_nonneg
  nlinarith

theorem pair_09_11 : 1 ≤ dist (point 9) (point 11) := by
  have hsq : 1 ≤ dist (point 9) (point 11) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 11) := dist_nonneg
  nlinarith

theorem pair_09_12 : 1 ≤ dist (point 9) (point 12) := by
  have hsq : 1 ≤ dist (point 9) (point 12) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 12) := dist_nonneg
  nlinarith

theorem pair_09_13 : 1 ≤ dist (point 9) (point 13) := by
  have hsq : 1 ≤ dist (point 9) (point 13) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 13) := dist_nonneg
  nlinarith

theorem pair_09_14 : 1 ≤ dist (point 9) (point 14) := by
  have hsq : 1 ≤ dist (point 9) (point 14) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 14) := dist_nonneg
  nlinarith

theorem pair_10_11 : 1 ≤ dist (point 10) (point 11) := by
  have hsq : 1 ≤ dist (point 10) (point 11) ^ 2 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 11) := dist_nonneg
  nlinarith

theorem pair_10_12 : 1 ≤ dist (point 10) (point 12) := by
  have hsq : 1 ≤ dist (point 10) (point 12) ^ 2 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 12) := dist_nonneg
  nlinarith

theorem pair_10_13 : 1 ≤ dist (point 10) (point 13) := by
  have hsq : 1 ≤ dist (point 10) (point 13) ^ 2 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 13) := dist_nonneg
  nlinarith

theorem pair_10_14 : 1 ≤ dist (point 10) (point 14) := by
  have hsq : 1 ≤ dist (point 10) (point 14) ^ 2 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 14) := dist_nonneg
  nlinarith

theorem pair_11_12 : 1 ≤ dist (point 11) (point 12) := by
  have hsq : 1 ≤ dist (point 11) (point 12) ^ 2 := by
    rw [show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 11) (point 12) := dist_nonneg
  nlinarith

theorem pair_11_13 : 1 ≤ dist (point 11) (point 13) := by
  have hsq : 1 ≤ dist (point 11) (point 13) ^ 2 := by
    rw [show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 11) (point 13) := dist_nonneg
  nlinarith

theorem pair_11_14 : 1 ≤ dist (point 11) (point 14) := by
  have hsq : 1 ≤ dist (point 11) (point 14) ^ 2 := by
    rw [show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 11) (point 14) := dist_nonneg
  nlinarith

theorem pair_12_13 : 1 ≤ dist (point 12) (point 13) := by
  have hsq : 1 ≤ dist (point 12) (point 13) ^ 2 := by
    rw [show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 12) (point 13) := dist_nonneg
  nlinarith

theorem pair_12_14 : 1 ≤ dist (point 12) (point 14) := by
  have hsq : 1 ≤ dist (point 12) (point 14) ^ 2 := by
    rw [show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 12) (point 14) := dist_nonneg
  nlinarith

theorem pair_13_14 : 1 ≤ dist (point 13) (point 14) := by
  have hsq : 1 ≤ dist (point 13) (point 14) ^ 2 := by
    rw [show point (13 : Fin 15) = pt (-s) (t + c) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 13) (point 14) := dist_nonneg
  nlinarith

theorem all_pair_lt (i j : Fin 15) (hij : i < j) :
    1 ≤ dist (point i) (point j) := by
  fin_cases i
  · fin_cases j
    · norm_num at hij
    · exact pair_00_01
    · exact pair_00_02
    · exact pair_00_03
    · exact pair_00_04
    · exact pair_00_05
    · exact pair_00_06
    · exact pair_00_07
    · exact pair_00_08
    · exact pair_00_09
    · exact pair_00_10
    · exact pair_00_11
    · exact pair_00_12
    · exact pair_00_13
    · exact pair_00_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · exact pair_01_02
    · exact pair_01_03
    · exact pair_01_04
    · exact pair_01_05
    · exact pair_01_06
    · exact pair_01_07
    · exact pair_01_08
    · exact pair_01_09
    · exact pair_01_10
    · exact pair_01_11
    · exact pair_01_12
    · exact pair_01_13
    · exact pair_01_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_02_03
    · exact pair_02_04
    · exact pair_02_05
    · exact pair_02_06
    · exact pair_02_07
    · exact pair_02_08
    · exact pair_02_09
    · exact pair_02_10
    · exact pair_02_11
    · exact pair_02_12
    · exact pair_02_13
    · exact pair_02_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_03_04
    · exact pair_03_05
    · exact pair_03_06
    · exact pair_03_07
    · exact pair_03_08
    · exact pair_03_09
    · exact pair_03_10
    · exact pair_03_11
    · exact pair_03_12
    · exact pair_03_13
    · exact pair_03_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_04_05
    · exact pair_04_06
    · exact pair_04_07
    · exact pair_04_08
    · exact pair_04_09
    · exact pair_04_10
    · exact pair_04_11
    · exact pair_04_12
    · exact pair_04_13
    · exact pair_04_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_05_06
    · exact pair_05_07
    · exact pair_05_08
    · exact pair_05_09
    · exact pair_05_10
    · exact pair_05_11
    · exact pair_05_12
    · exact pair_05_13
    · exact pair_05_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_06_07
    · exact pair_06_08
    · exact pair_06_09
    · exact pair_06_10
    · exact pair_06_11
    · exact pair_06_12
    · exact pair_06_13
    · exact pair_06_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_07_08
    · exact pair_07_09
    · exact pair_07_10
    · exact pair_07_11
    · exact pair_07_12
    · exact pair_07_13
    · exact pair_07_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_08_09
    · exact pair_08_10
    · exact pair_08_11
    · exact pair_08_12
    · exact pair_08_13
    · exact pair_08_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_09_10
    · exact pair_09_11
    · exact pair_09_12
    · exact pair_09_13
    · exact pair_09_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_10_11
    · exact pair_10_12
    · exact pair_10_13
    · exact pair_10_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_11_12
    · exact pair_11_13
    · exact pair_11_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_12_13
    · exact pair_12_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact pair_13_14
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij

theorem separated_point : Separated point 1 := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact all_pair_lt i j hlt
  · simpa [dist_comm] using all_pair_lt j i hgt

end CP15.Candidate
