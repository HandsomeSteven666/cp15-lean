import CP15.CandidateExact

set_option maxHeartbeats 2000000

namespace CP15.Candidate

theorem classified_00_01 : dist (point 0) (point 1) = 1 := by
  have hsq : dist (point 0) (point 1) ^ 2 = 1 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 1) := dist_nonneg
  nlinarith

theorem classified_00_02 : 1 < dist (point 0) (point 2) := by
  have hsq : 1 < dist (point 0) (point 2) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 2) := dist_nonneg
  nlinarith

theorem classified_00_03 : 1 < dist (point 0) (point 3) := by
  have hsq : 1 < dist (point 0) (point 3) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 3) := dist_nonneg
  nlinarith

theorem classified_00_04 : dist (point 0) (point 4) = 1 := by
  have hsq : dist (point 0) (point 4) ^ 2 = 1 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 4) := dist_nonneg
  nlinarith

theorem classified_00_05 : 1 < dist (point 0) (point 5) := by
  have hsq : 1 < dist (point 0) (point 5) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 5) := dist_nonneg
  nlinarith

theorem classified_00_06 : 1 < dist (point 0) (point 6) := by
  have hsq : 1 < dist (point 0) (point 6) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 6) := dist_nonneg
  nlinarith

theorem classified_00_07 : 1 < dist (point 0) (point 7) := by
  have hsq : 1 < dist (point 0) (point 7) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 7) := dist_nonneg
  nlinarith

theorem classified_00_08 : 1 < dist (point 0) (point 8) := by
  have hsq : 1 < dist (point 0) (point 8) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 8) := dist_nonneg
  nlinarith

theorem classified_00_09 : 1 < dist (point 0) (point 9) := by
  have hsq : 1 < dist (point 0) (point 9) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 9) := dist_nonneg
  nlinarith

theorem classified_00_10 : 1 < dist (point 0) (point 10) := by
  have hsq : 1 < dist (point 0) (point 10) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 10) := dist_nonneg
  nlinarith

theorem classified_00_11 : 1 < dist (point 0) (point 11) := by
  have hsq : 1 < dist (point 0) (point 11) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 11) := dist_nonneg
  nlinarith

theorem classified_00_12 : 1 < dist (point 0) (point 12) := by
  have hsq : 1 < dist (point 0) (point 12) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 12) := dist_nonneg
  nlinarith

theorem classified_00_13 : 1 < dist (point 0) (point 13) := by
  have hsq : 1 < dist (point 0) (point 13) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 13) := dist_nonneg
  nlinarith

theorem classified_00_14 : 1 < dist (point 0) (point 14) := by
  have hsq : 1 < dist (point 0) (point 14) ^ 2 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 0) (point 14) := dist_nonneg
  nlinarith

theorem classified_01_02 : 1 < dist (point 1) (point 2) := by
  have hsq : 1 < dist (point 1) (point 2) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 2) := dist_nonneg
  nlinarith

theorem classified_01_03 : 1 < dist (point 1) (point 3) := by
  have hsq : 1 < dist (point 1) (point 3) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 3) := dist_nonneg
  nlinarith

theorem classified_01_04 : 1 < dist (point 1) (point 4) := by
  have hsq : 1 < dist (point 1) (point 4) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 4) := dist_nonneg
  nlinarith

theorem classified_01_05 : dist (point 1) (point 5) = 1 := by
  have hsq : dist (point 1) (point 5) ^ 2 = 1 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 5) := dist_nonneg
  nlinarith

theorem classified_01_06 : 1 < dist (point 1) (point 6) := by
  have hsq : 1 < dist (point 1) (point 6) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 6) := dist_nonneg
  nlinarith

theorem classified_01_07 : 1 < dist (point 1) (point 7) := by
  have hsq : 1 < dist (point 1) (point 7) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 7) := dist_nonneg
  nlinarith

theorem classified_01_08 : 1 < dist (point 1) (point 8) := by
  have hsq : 1 < dist (point 1) (point 8) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 8) := dist_nonneg
  nlinarith

theorem classified_01_09 : 1 < dist (point 1) (point 9) := by
  have hsq : 1 < dist (point 1) (point 9) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 9) := dist_nonneg
  nlinarith

theorem classified_01_10 : 1 < dist (point 1) (point 10) := by
  have hsq : 1 < dist (point 1) (point 10) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 10) := dist_nonneg
  nlinarith

theorem classified_01_11 : 1 < dist (point 1) (point 11) := by
  have hsq : 1 < dist (point 1) (point 11) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 11) := dist_nonneg
  nlinarith

theorem classified_01_12 : 1 < dist (point 1) (point 12) := by
  have hsq : 1 < dist (point 1) (point 12) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 12) := dist_nonneg
  nlinarith

theorem classified_01_13 : 1 < dist (point 1) (point 13) := by
  have hsq : 1 < dist (point 1) (point 13) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 13) := dist_nonneg
  nlinarith

theorem classified_01_14 : 1 < dist (point 1) (point 14) := by
  have hsq : 1 < dist (point 1) (point 14) ^ 2 := by
    rw [show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 1) (point 14) := dist_nonneg
  nlinarith

theorem classified_02_03 : 1 < dist (point 2) (point 3) := by
  have hsq : 1 < dist (point 2) (point 3) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 3) := dist_nonneg
  nlinarith

theorem classified_02_04 : dist (point 2) (point 4) = 1 := by
  have hsq : dist (point 2) (point 4) ^ 2 = 1 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 4) := dist_nonneg
  nlinarith

theorem classified_02_05 : 1 < dist (point 2) (point 5) := by
  have hsq : 1 < dist (point 2) (point 5) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 5) := dist_nonneg
  nlinarith

theorem classified_02_06 : dist (point 2) (point 6) = 1 := by
  have hsq : dist (point 2) (point 6) ^ 2 = 1 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 6) := dist_nonneg
  nlinarith

theorem classified_02_07 : 1 < dist (point 2) (point 7) := by
  have hsq : 1 < dist (point 2) (point 7) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 7) := dist_nonneg
  nlinarith

theorem classified_02_08 : 1 < dist (point 2) (point 8) := by
  have hsq : 1 < dist (point 2) (point 8) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 8) := dist_nonneg
  nlinarith

theorem classified_02_09 : 1 < dist (point 2) (point 9) := by
  have hsq : 1 < dist (point 2) (point 9) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 9) := dist_nonneg
  nlinarith

theorem classified_02_10 : 1 < dist (point 2) (point 10) := by
  have hsq : 1 < dist (point 2) (point 10) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 10) := dist_nonneg
  nlinarith

theorem classified_02_11 : 1 < dist (point 2) (point 11) := by
  have hsq : 1 < dist (point 2) (point 11) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 11) := dist_nonneg
  nlinarith

theorem classified_02_12 : 1 < dist (point 2) (point 12) := by
  have hsq : 1 < dist (point 2) (point 12) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 12) := dist_nonneg
  nlinarith

theorem classified_02_13 : 1 < dist (point 2) (point 13) := by
  have hsq : 1 < dist (point 2) (point 13) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 13) := dist_nonneg
  nlinarith

theorem classified_02_14 : 1 < dist (point 2) (point 14) := by
  have hsq : 1 < dist (point 2) (point 14) ^ 2 := by
    rw [show point (2 : Fin 15) = pt (-1 / 2 - u) (t - s - u - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 2) (point 14) := dist_nonneg
  nlinarith

theorem classified_03_04 : 1 < dist (point 3) (point 4) := by
  have hsq : 1 < dist (point 3) (point 4) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 4) := dist_nonneg
  nlinarith

theorem classified_03_05 : dist (point 3) (point 5) = 1 := by
  have hsq : dist (point 3) (point 5) ^ 2 = 1 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 5) := dist_nonneg
  nlinarith

theorem classified_03_06 : 1 < dist (point 3) (point 6) := by
  have hsq : 1 < dist (point 3) (point 6) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 6) := dist_nonneg
  nlinarith

theorem classified_03_07 : dist (point 3) (point 7) = 1 := by
  have hsq : dist (point 3) (point 7) ^ 2 = 1 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 7) := dist_nonneg
  nlinarith

theorem classified_03_08 : 1 < dist (point 3) (point 8) := by
  have hsq : 1 < dist (point 3) (point 8) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 8) := dist_nonneg
  nlinarith

theorem classified_03_09 : 1 < dist (point 3) (point 9) := by
  have hsq : 1 < dist (point 3) (point 9) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 9) := dist_nonneg
  nlinarith

theorem classified_03_10 : 1 < dist (point 3) (point 10) := by
  have hsq : 1 < dist (point 3) (point 10) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 10) := dist_nonneg
  nlinarith

theorem classified_03_11 : 1 < dist (point 3) (point 11) := by
  have hsq : 1 < dist (point 3) (point 11) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 11) := dist_nonneg
  nlinarith

theorem classified_03_12 : 1 < dist (point 3) (point 12) := by
  have hsq : 1 < dist (point 3) (point 12) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 12) := dist_nonneg
  nlinarith

theorem classified_03_13 : 1 < dist (point 3) (point 13) := by
  have hsq : 1 < dist (point 3) (point 13) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 13) := dist_nonneg
  nlinarith

theorem classified_03_14 : 1 < dist (point 3) (point 14) := by
  have hsq : 1 < dist (point 3) (point 14) ^ 2 := by
    rw [show point (3 : Fin 15) = pt (1 / 2 + u) (t - s - u - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 3) (point 14) := dist_nonneg
  nlinarith

theorem classified_04_05 : dist (point 4) (point 5) = 1 := by
  have hsq : dist (point 4) (point 5) ^ 2 = 1 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 5) := dist_nonneg
  nlinarith

theorem classified_04_06 : 1 < dist (point 4) (point 6) := by
  have hsq : 1 < dist (point 4) (point 6) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 6) := dist_nonneg
  nlinarith

theorem classified_04_07 : 1 < dist (point 4) (point 7) := by
  have hsq : 1 < dist (point 4) (point 7) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 7) := dist_nonneg
  nlinarith

theorem classified_04_08 : dist (point 4) (point 8) = 1 := by
  have hsq : dist (point 4) (point 8) ^ 2 = 1 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 8) := dist_nonneg
  nlinarith

theorem classified_04_09 : 1 < dist (point 4) (point 9) := by
  have hsq : 1 < dist (point 4) (point 9) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 9) := dist_nonneg
  nlinarith

theorem classified_04_10 : 1 < dist (point 4) (point 10) := by
  have hsq : 1 < dist (point 4) (point 10) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 10) := dist_nonneg
  nlinarith

theorem classified_04_11 : 1 < dist (point 4) (point 11) := by
  have hsq : 1 < dist (point 4) (point 11) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 11) := dist_nonneg
  nlinarith

theorem classified_04_12 : 1 < dist (point 4) (point 12) := by
  have hsq : 1 < dist (point 4) (point 12) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 12) := dist_nonneg
  nlinarith

theorem classified_04_13 : 1 < dist (point 4) (point 13) := by
  have hsq : 1 < dist (point 4) (point 13) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 13) := dist_nonneg
  nlinarith

theorem classified_04_14 : 1 < dist (point 4) (point 14) := by
  have hsq : 1 < dist (point 4) (point 14) ^ 2 := by
    rw [show point (4 : Fin 15) = pt (-1 / 2) (t - s - u) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 4) (point 14) := dist_nonneg
  nlinarith

theorem classified_05_06 : 1 < dist (point 5) (point 6) := by
  have hsq : 1 < dist (point 5) (point 6) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 6) := dist_nonneg
  nlinarith

theorem classified_05_07 : 1 < dist (point 5) (point 7) := by
  have hsq : 1 < dist (point 5) (point 7) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 7) := dist_nonneg
  nlinarith

theorem classified_05_08 : 1 < dist (point 5) (point 8) := by
  have hsq : 1 < dist (point 5) (point 8) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 8) := dist_nonneg
  nlinarith

theorem classified_05_09 : dist (point 5) (point 9) = 1 := by
  have hsq : dist (point 5) (point 9) ^ 2 = 1 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 9) := dist_nonneg
  nlinarith

theorem classified_05_10 : 1 < dist (point 5) (point 10) := by
  have hsq : 1 < dist (point 5) (point 10) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 10) := dist_nonneg
  nlinarith

theorem classified_05_11 : 1 < dist (point 5) (point 11) := by
  have hsq : 1 < dist (point 5) (point 11) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 11) := dist_nonneg
  nlinarith

theorem classified_05_12 : 1 < dist (point 5) (point 12) := by
  have hsq : 1 < dist (point 5) (point 12) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 12) := dist_nonneg
  nlinarith

theorem classified_05_13 : 1 < dist (point 5) (point 13) := by
  have hsq : 1 < dist (point 5) (point 13) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 13) := dist_nonneg
  nlinarith

theorem classified_05_14 : 1 < dist (point 5) (point 14) := by
  have hsq : 1 < dist (point 5) (point 14) ^ 2 := by
    rw [show point (5 : Fin 15) = pt (1 / 2) (t - s - u) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 5) (point 14) := dist_nonneg
  nlinarith

theorem classified_06_07 : 1 < dist (point 6) (point 7) := by
  have hsq : 1 < dist (point 6) (point 7) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 7) := dist_nonneg
  nlinarith

theorem classified_06_08 : dist (point 6) (point 8) = 1 := by
  have hsq : dist (point 6) (point 8) ^ 2 = 1 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    have hc : c = v + 1 / 2 := by linarith [c_sub_v]
    rw [hc]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 8) := dist_nonneg
  nlinarith

theorem classified_06_09 : 1 < dist (point 6) (point 9) := by
  have hsq : 1 < dist (point 6) (point 9) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 9) := dist_nonneg
  nlinarith

theorem classified_06_10 : 1 < dist (point 6) (point 10) := by
  have hsq : 1 < dist (point 6) (point 10) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 10) := dist_nonneg
  nlinarith

theorem classified_06_11 : 1 < dist (point 6) (point 11) := by
  have hsq : 1 < dist (point 6) (point 11) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 11) := dist_nonneg
  nlinarith

theorem classified_06_12 : 1 < dist (point 6) (point 12) := by
  have hsq : 1 < dist (point 6) (point 12) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 12) := dist_nonneg
  nlinarith

theorem classified_06_13 : 1 < dist (point 6) (point 13) := by
  have hsq : 1 < dist (point 6) (point 13) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 13) := dist_nonneg
  nlinarith

theorem classified_06_14 : 1 < dist (point 6) (point 14) := by
  have hsq : 1 < dist (point 6) (point 14) ^ 2 := by
    rw [show point (6 : Fin 15) = pt (-1 / 2 - u - v) (t - s - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 6) (point 14) := dist_nonneg
  nlinarith

theorem classified_07_08 : 1 < dist (point 7) (point 8) := by
  have hsq : 1 < dist (point 7) (point 8) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (8 : Fin 15) = pt (-c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 8) := dist_nonneg
  nlinarith

theorem classified_07_09 : dist (point 7) (point 9) = 1 := by
  have hsq : dist (point 7) (point 9) ^ 2 = 1 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    have hc : c = v + 1 / 2 := by linarith [c_sub_v]
    rw [hc]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 9) := dist_nonneg
  nlinarith

theorem classified_07_10 : 1 < dist (point 7) (point 10) := by
  have hsq : 1 < dist (point 7) (point 10) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 10) := dist_nonneg
  nlinarith

theorem classified_07_11 : 1 < dist (point 7) (point 11) := by
  have hsq : 1 < dist (point 7) (point 11) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 11) := dist_nonneg
  nlinarith

theorem classified_07_12 : 1 < dist (point 7) (point 12) := by
  have hsq : 1 < dist (point 7) (point 12) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 12) := dist_nonneg
  nlinarith

theorem classified_07_13 : 1 < dist (point 7) (point 13) := by
  have hsq : 1 < dist (point 7) (point 13) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 13) := dist_nonneg
  nlinarith

theorem classified_07_14 : 1 < dist (point 7) (point 14) := by
  have hsq : 1 < dist (point 7) (point 14) ^ 2 := by
    rw [show point (7 : Fin 15) = pt (1 / 2 + u + v) (t - s - v) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 7) (point 14) := dist_nonneg
  nlinarith

theorem classified_08_09 : 1 < dist (point 8) (point 9) := by
  have hsq : 1 < dist (point 8) (point 9) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (9 : Fin 15) = pt (c) (t - s) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 9) := dist_nonneg
  nlinarith

theorem classified_08_10 : dist (point 8) (point 10) = 1 := by
  have hsq : dist (point 8) (point 10) ^ 2 = 1 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 10) := dist_nonneg
  nlinarith

theorem classified_08_11 : dist (point 8) (point 11) = 1 := by
  have hsq : dist (point 8) (point 11) ^ 2 = 1 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 11) := dist_nonneg
  nlinarith

theorem classified_08_12 : 1 < dist (point 8) (point 12) := by
  have hsq : 1 < dist (point 8) (point 12) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 12) := dist_nonneg
  nlinarith

theorem classified_08_13 : 1 < dist (point 8) (point 13) := by
  have hsq : 1 < dist (point 8) (point 13) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 13) := dist_nonneg
  nlinarith

theorem classified_08_14 : 1 < dist (point 8) (point 14) := by
  have hsq : 1 < dist (point 8) (point 14) ^ 2 := by
    rw [show point (8 : Fin 15) = pt (-c) (t - s) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 8) (point 14) := dist_nonneg
  nlinarith

theorem classified_09_10 : dist (point 9) (point 10) = 1 := by
  have hsq : dist (point 9) (point 10) ^ 2 = 1 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (10 : Fin 15) = pt (0) (t) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 10) := dist_nonneg
  nlinarith

theorem classified_09_11 : 1 < dist (point 9) (point 11) := by
  have hsq : 1 < dist (point 9) (point 11) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 11) := dist_nonneg
  nlinarith

theorem classified_09_12 : dist (point 9) (point 12) = 1 := by
  have hsq : dist (point 9) (point 12) ^ 2 = 1 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 12) := dist_nonneg
  nlinarith

theorem classified_09_13 : 1 < dist (point 9) (point 13) := by
  have hsq : 1 < dist (point 9) (point 13) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 13) := dist_nonneg
  nlinarith

theorem classified_09_14 : 1 < dist (point 9) (point 14) := by
  have hsq : 1 < dist (point 9) (point 14) ^ 2 := by
    rw [show point (9 : Fin 15) = pt (c) (t - s) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 9) (point 14) := dist_nonneg
  nlinarith

theorem classified_10_11 : 1 < dist (point 10) (point 11) := by
  have hsq : 1 < dist (point 10) (point 11) ^ 2 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 11) := dist_nonneg
  nlinarith

theorem classified_10_12 : 1 < dist (point 10) (point 12) := by
  have hsq : 1 < dist (point 10) (point 12) ^ 2 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 12) := dist_nonneg
  nlinarith

theorem classified_10_13 : dist (point 10) (point 13) = 1 := by
  have hsq : dist (point 10) (point 13) ^ 2 = 1 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 13) := dist_nonneg
  nlinarith

theorem classified_10_14 : dist (point 10) (point 14) = 1 := by
  have hsq : dist (point 10) (point 14) ^ 2 = 1 := by
    rw [show point (10 : Fin 15) = pt (0) (t) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 10) (point 14) := dist_nonneg
  nlinarith

theorem classified_11_12 : 1 < dist (point 11) (point 12) := by
  have hsq : 1 < dist (point 11) (point 12) ^ 2 := by
    rw [show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl,
      show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 11) (point 12) := dist_nonneg
  nlinarith

theorem classified_11_13 : dist (point 11) (point 13) = 1 := by
  have hsq : dist (point 11) (point 13) ^ 2 = 1 := by
    rw [show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 11) (point 13) := dist_nonneg
  nlinarith

theorem classified_11_14 : 1 < dist (point 11) (point 14) := by
  have hsq : 1 < dist (point 11) (point 14) ^ 2 := by
    rw [show point (11 : Fin 15) = pt (-c - s) (t - s + c) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 11) (point 14) := dist_nonneg
  nlinarith

theorem classified_12_13 : 1 < dist (point 12) (point 13) := by
  have hsq : 1 < dist (point 12) (point 13) ^ 2 := by
    rw [show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl,
      show point (13 : Fin 15) = pt (-s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 12) (point 13) := dist_nonneg
  nlinarith

theorem classified_12_14 : dist (point 12) (point 14) = 1 := by
  have hsq : dist (point 12) (point 14) ^ 2 = 1 := by
    rw [show point (12 : Fin 15) = pt (c + s) (t - s + c) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 12) (point 14) := dist_nonneg
  nlinarith

theorem classified_13_14 : 1 < dist (point 13) (point 14) := by
  have hsq : 1 < dist (point 13) (point 14) ^ 2 := by
    rw [show point (13 : Fin 15) = pt (-s) (t + c) by rfl,
      show point (14 : Fin 15) = pt (s) (t + c) by rfl, dist_pt_sq]
    rcases simple_bounds with
      ⟨hslo, hshi, hclo, hchi, hulo, huhi, hvlo, hvhi⟩
    nlinarith [pentagon_identity, square_identity, c_sub_v,
      two_s_c, two_u_v, two_s_sq, two_c_sq]
  have hn : 0 ≤ dist (point 13) (point 14) := dist_nonneg
  nlinarith

def contactPairs : Finset (Fin 15 × Fin 15) :=
  {(0, 1), (0, 4), (1, 5), (2, 4), (2, 6), (3, 5), (3, 7), (4, 5), (4, 8), (5, 9), (6, 8), (7, 9), (8, 10), (8, 11), (9, 10), (9, 12), (10, 13), (10, 14), (11, 13), (12, 14)}

theorem contactPairs_card : contactPairs.card = 20 := by decide

theorem contact_iff (i j : Fin 15) (hij : i < j) :
    dist (point i) (point j) = 1 ↔ (i, j) ∈ contactPairs := by
  fin_cases i
  · fin_cases j
    · norm_num at hij
    · simpa [contactPairs] using classified_00_01
    · simpa [contactPairs] using (ne_of_gt classified_00_02)
    · simpa [contactPairs] using (ne_of_gt classified_00_03)
    · simpa [contactPairs] using classified_00_04
    · simpa [contactPairs] using (ne_of_gt classified_00_05)
    · simpa [contactPairs] using (ne_of_gt classified_00_06)
    · simpa [contactPairs] using (ne_of_gt classified_00_07)
    · simpa [contactPairs] using (ne_of_gt classified_00_08)
    · simpa [contactPairs] using (ne_of_gt classified_00_09)
    · simpa [contactPairs] using (ne_of_gt classified_00_10)
    · simpa [contactPairs] using (ne_of_gt classified_00_11)
    · simpa [contactPairs] using (ne_of_gt classified_00_12)
    · simpa [contactPairs] using (ne_of_gt classified_00_13)
    · simpa [contactPairs] using (ne_of_gt classified_00_14)
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · simpa [contactPairs] using (ne_of_gt classified_01_02)
    · simpa [contactPairs] using (ne_of_gt classified_01_03)
    · simpa [contactPairs] using (ne_of_gt classified_01_04)
    · simpa [contactPairs] using classified_01_05
    · simpa [contactPairs] using (ne_of_gt classified_01_06)
    · simpa [contactPairs] using (ne_of_gt classified_01_07)
    · simpa [contactPairs] using (ne_of_gt classified_01_08)
    · simpa [contactPairs] using (ne_of_gt classified_01_09)
    · simpa [contactPairs] using (ne_of_gt classified_01_10)
    · simpa [contactPairs] using (ne_of_gt classified_01_11)
    · simpa [contactPairs] using (ne_of_gt classified_01_12)
    · simpa [contactPairs] using (ne_of_gt classified_01_13)
    · simpa [contactPairs] using (ne_of_gt classified_01_14)
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · simpa [contactPairs] using (ne_of_gt classified_02_03)
    · simpa [contactPairs] using classified_02_04
    · simpa [contactPairs] using (ne_of_gt classified_02_05)
    · simpa [contactPairs] using classified_02_06
    · simpa [contactPairs] using (ne_of_gt classified_02_07)
    · simpa [contactPairs] using (ne_of_gt classified_02_08)
    · simpa [contactPairs] using (ne_of_gt classified_02_09)
    · simpa [contactPairs] using (ne_of_gt classified_02_10)
    · simpa [contactPairs] using (ne_of_gt classified_02_11)
    · simpa [contactPairs] using (ne_of_gt classified_02_12)
    · simpa [contactPairs] using (ne_of_gt classified_02_13)
    · simpa [contactPairs] using (ne_of_gt classified_02_14)
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · simpa [contactPairs] using (ne_of_gt classified_03_04)
    · simpa [contactPairs] using classified_03_05
    · simpa [contactPairs] using (ne_of_gt classified_03_06)
    · simpa [contactPairs] using classified_03_07
    · simpa [contactPairs] using (ne_of_gt classified_03_08)
    · simpa [contactPairs] using (ne_of_gt classified_03_09)
    · simpa [contactPairs] using (ne_of_gt classified_03_10)
    · simpa [contactPairs] using (ne_of_gt classified_03_11)
    · simpa [contactPairs] using (ne_of_gt classified_03_12)
    · simpa [contactPairs] using (ne_of_gt classified_03_13)
    · simpa [contactPairs] using (ne_of_gt classified_03_14)
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · simpa [contactPairs] using classified_04_05
    · simpa [contactPairs] using (ne_of_gt classified_04_06)
    · simpa [contactPairs] using (ne_of_gt classified_04_07)
    · simpa [contactPairs] using classified_04_08
    · simpa [contactPairs] using (ne_of_gt classified_04_09)
    · simpa [contactPairs] using (ne_of_gt classified_04_10)
    · simpa [contactPairs] using (ne_of_gt classified_04_11)
    · simpa [contactPairs] using (ne_of_gt classified_04_12)
    · simpa [contactPairs] using (ne_of_gt classified_04_13)
    · simpa [contactPairs] using (ne_of_gt classified_04_14)
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · simpa [contactPairs] using (ne_of_gt classified_05_06)
    · simpa [contactPairs] using (ne_of_gt classified_05_07)
    · simpa [contactPairs] using (ne_of_gt classified_05_08)
    · simpa [contactPairs] using classified_05_09
    · simpa [contactPairs] using (ne_of_gt classified_05_10)
    · simpa [contactPairs] using (ne_of_gt classified_05_11)
    · simpa [contactPairs] using (ne_of_gt classified_05_12)
    · simpa [contactPairs] using (ne_of_gt classified_05_13)
    · simpa [contactPairs] using (ne_of_gt classified_05_14)
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · simpa [contactPairs] using (ne_of_gt classified_06_07)
    · simpa [contactPairs] using classified_06_08
    · simpa [contactPairs] using (ne_of_gt classified_06_09)
    · simpa [contactPairs] using (ne_of_gt classified_06_10)
    · simpa [contactPairs] using (ne_of_gt classified_06_11)
    · simpa [contactPairs] using (ne_of_gt classified_06_12)
    · simpa [contactPairs] using (ne_of_gt classified_06_13)
    · simpa [contactPairs] using (ne_of_gt classified_06_14)
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · simpa [contactPairs] using (ne_of_gt classified_07_08)
    · simpa [contactPairs] using classified_07_09
    · simpa [contactPairs] using (ne_of_gt classified_07_10)
    · simpa [contactPairs] using (ne_of_gt classified_07_11)
    · simpa [contactPairs] using (ne_of_gt classified_07_12)
    · simpa [contactPairs] using (ne_of_gt classified_07_13)
    · simpa [contactPairs] using (ne_of_gt classified_07_14)
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
    · simpa [contactPairs] using (ne_of_gt classified_08_09)
    · simpa [contactPairs] using classified_08_10
    · simpa [contactPairs] using classified_08_11
    · simpa [contactPairs] using (ne_of_gt classified_08_12)
    · simpa [contactPairs] using (ne_of_gt classified_08_13)
    · simpa [contactPairs] using (ne_of_gt classified_08_14)
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
    · simpa [contactPairs] using classified_09_10
    · simpa [contactPairs] using (ne_of_gt classified_09_11)
    · simpa [contactPairs] using classified_09_12
    · simpa [contactPairs] using (ne_of_gt classified_09_13)
    · simpa [contactPairs] using (ne_of_gt classified_09_14)
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
    · simpa [contactPairs] using (ne_of_gt classified_10_11)
    · simpa [contactPairs] using (ne_of_gt classified_10_12)
    · simpa [contactPairs] using classified_10_13
    · simpa [contactPairs] using classified_10_14
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
    · simpa [contactPairs] using (ne_of_gt classified_11_12)
    · simpa [contactPairs] using classified_11_13
    · simpa [contactPairs] using (ne_of_gt classified_11_14)
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
    · simpa [contactPairs] using (ne_of_gt classified_12_13)
    · simpa [contactPairs] using classified_12_14
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
    · simpa [contactPairs] using (ne_of_gt classified_13_14)
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

end CP15.Candidate
