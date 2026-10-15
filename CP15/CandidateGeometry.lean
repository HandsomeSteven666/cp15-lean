import CP15.CandidateAlgebra

namespace CP15.Candidate

def pt (x y : ℝ) : Plane := !₂[x, y]

theorem norm_pt_sq (x y : ℝ) : ‖pt x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  simpa [pt, Fin.sum_univ_two] using
    EuclideanSpace.real_norm_sq_eq (pt x y)

theorem dist_pt_sq (x y a b : ℝ) :
    dist (pt x y) (pt a b) ^ 2 = (x - a) ^ 2 + (y - b) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [pt, Fin.sum_univ_two]

/-- The exact fifteen-center candidate at minimum separation one, using
zero-based Lean indices for the one-based labels in the research report. -/
noncomputable def point (i : Fin 15) : Plane :=
  match i.val with
  | 0 => pt (-1 / 2) (t - s - u - 1)
  | 1 => pt (1 / 2) (t - s - u - 1)
  | 2 => pt (-1 / 2 - u) (t - s - u - v)
  | 3 => pt (1 / 2 + u) (t - s - u - v)
  | 4 => pt (-1 / 2) (t - s - u)
  | 5 => pt (1 / 2) (t - s - u)
  | 6 => pt (-1 / 2 - u - v) (t - s - v)
  | 7 => pt (1 / 2 + u + v) (t - s - v)
  | 8 => pt (-c) (t - s)
  | 9 => pt c (t - s)
  | 10 => pt 0 t
  | 11 => pt (-c - s) (t - s + c)
  | 12 => pt (c + s) (t - s + c)
  | 13 => pt (-s) (t + c)
  | 14 => pt s (t + c)
  | _ => 0

noncomputable def pointAtSeparationTwo (i : Fin 15) : Plane :=
  (2 : ℝ) • point i

theorem upper_left_norm_sq : ‖point 13‖ ^ 2 = rho ^ 2 := by
  rw [show point (13 : Fin 15) = pt (-s) (t + c) by rfl,
    norm_pt_sq, rho_sq]
  ring

theorem upper_right_norm_sq : ‖point 14‖ ^ 2 = rho ^ 2 := by
  rw [show point (14 : Fin 15) = pt s (t + c) by rfl,
    norm_pt_sq, rho_sq]

theorem first_outer_contact : dist (point 0) (point 1) = 1 := by
  have hsq : dist (point 0) (point 1) ^ 2 = 1 := by
    rw [show point (0 : Fin 15) = pt (-1 / 2) (t - s - u - 1) by rfl,
      show point (1 : Fin 15) = pt (1 / 2) (t - s - u - 1) by rfl,
      dist_pt_sq]
    ring
  have hn : 0 ≤ dist (point 0) (point 1) := dist_nonneg
  nlinarith

end CP15.Candidate
