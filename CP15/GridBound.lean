import CP15.Definitions

namespace CP15

private noncomputable def coordBin (x : ℝ) : Fin 3 :=
  if x < -(2 / 3 : ℝ) then 0 else if x < 2 / 3 then 1 else 2

private theorem same_bin_difference {x y : ℝ}
    (hxlo : -2 ≤ x) (hxhi : x ≤ 2)
    (hylo : -2 ≤ y) (hyhi : y ≤ 2)
    (hbin : coordBin x = coordBin y) :
    -(4 / 3 : ℝ) ≤ x - y ∧ x - y ≤ 4 / 3 := by
  unfold coordBin at hbin
  split_ifs at hbin <;> norm_num at hbin <;>
    constructor <;> linarith

private noncomputable def cell (p : Fin 15 → Plane) (i : Fin 15) : Fin 3 × Fin 3 :=
  (coordBin (p i 0), coordBin (p i 1))

/-- A three-by-three square partition proves that fifteen points with
separation two cannot lie in a disk of radius at most two. -/
theorem centerFeasible_radius_gt_two {b : ℝ}
    (h : CenterFeasible 15 b) : 2 < b := by
  by_contra hnot
  have hb : b ≤ 2 := le_of_not_gt hnot
  rcases h with ⟨p, hp, hs⟩
  obtain ⟨i, j, hij, hcell⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (cell p) (by decide : 9 < 15)
  have hcoord (k : Fin 2) (a : Fin 15) :
      -2 ≤ p a k ∧ p a k ≤ 2 := by
    have hnorm : ‖p a k‖ ≤ ‖p a‖ := PiLp.norm_apply_le (p a) k
    have hle : ‖p a k‖ ≤ 2 := hnorm.trans ((hp a).trans hb)
    rw [Real.norm_eq_abs] at hle
    exact abs_le.mp hle
  have h0bin : coordBin (p i 0) = coordBin (p j 0) :=
    congrArg Prod.fst hcell
  have h1bin : coordBin (p i 1) = coordBin (p j 1) :=
    congrArg Prod.snd hcell
  obtain ⟨h0lo, h0hi⟩ := same_bin_difference
    (hcoord 0 i).1 (hcoord 0 i).2
    (hcoord 0 j).1 (hcoord 0 j).2 h0bin
  obtain ⟨h1lo, h1hi⟩ := same_bin_difference
    (hcoord 1 i).1 (hcoord 1 i).2
    (hcoord 1 j).1 (hcoord 1 j).2 h1bin
  have h0sq : (p i 0 - p j 0) ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by
    have hprod : 0 ≤ ((4 / 3 : ℝ) - (p i 0 - p j 0)) *
        ((4 / 3 : ℝ) + (p i 0 - p j 0)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h1sq : (p i 1 - p j 1) ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by
    have hprod : 0 ≤ ((4 / 3 : ℝ) - (p i 1 - p j 1)) *
        ((4 / 3 : ℝ) + (p i 1 - p j 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hdist : dist (p i) (p j) ^ 2 =
      (p i 0 - p j 0) ^ 2 + (p i 1 - p j 1) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hsep := hs i j hij
  have hdist_nonneg : 0 ≤ dist (p i) (p j) := dist_nonneg
  nlinarith

end CP15
