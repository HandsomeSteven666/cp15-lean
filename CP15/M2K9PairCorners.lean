import CP15.M2K9AngleBounds
import CP15.M3K8

namespace CP15

def pairExpr (r s c : ℝ) : ℝ := r ^ 2 + s ^ 2 - 2 * c * r * s

private theorem pairExpr_comm (r s c : ℝ) :
    pairExpr r s c = pairExpr s r c := by
  unfold pairExpr
  ring

/-- Separate convexity, proved algebraically, reduces one radius
interval to its two endpoints. -/
theorem pairExpr_le_endpoint_max
    (a r b s c : ℝ) (har : a ≤ r) (hrb : r ≤ b) :
    pairExpr r s c ≤
      max (pairExpr a s c) (pairExpr b s c) := by
  by_cases hder : r + a - 2 * c * s ≤ 0
  · have hprod := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr har) hder
    have hle : pairExpr r s c ≤ pairExpr a s c := by
      unfold pairExpr
      nlinarith
    exact hle.trans (le_max_left _ _)
  · have hpos : 0 ≤ b + r - 2 * c * s := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hrb) hpos
    have hle : pairExpr r s c ≤ pairExpr b s c := by
      unfold pairExpr
      nlinarith
    exact hle.trans (le_max_right _ _)

/-- A four-corner exact rational check controls every point of a closed
radius rectangle; no numerical optimization is used. -/
theorem pairExpr_lt_four_of_corners
    (a r b d s e c : ℝ)
    (har : a ≤ r) (hrb : r ≤ b)
    (hds : d ≤ s) (hse : s ≤ e)
    (had : pairExpr a d c < 4)
    (hae : pairExpr a e c < 4)
    (hbd : pairExpr b d c < 4)
    (hbe : pairExpr b e c < 4) :
    pairExpr r s c < 4 := by
  have hs := pairExpr_le_endpoint_max d s e r c hds hse
  rw [pairExpr_comm s r c, pairExpr_comm d r c,
    pairExpr_comm e r c] at hs
  have ha := pairExpr_le_endpoint_max a r b d c har hrb
  have he := pairExpr_le_endpoint_max a r b e c har hrb
  have hadmax : max (pairExpr a d c) (pairExpr b d c) < 4 :=
    max_lt had hbd
  have haemax : max (pairExpr a e c) (pairExpr b e c) < 4 :=
    max_lt hae hbe
  have had' : pairExpr r d c < 4 := ha.trans_lt hadmax
  have hae' : pairExpr r e c < 4 := he.trans_lt haemax
  exact hs.trans_lt (max_lt had' hae')

theorem shared_AH_corner
    (r s : ℝ)
    (hrlo : (699 / 1000 : ℝ) ≤ r)
    (hrhi : r ≤ 1301 / 1000)
    (hslo : (2 : ℝ) ≤ s)
    (hshi : s ≤ 2385436 / 1000000) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (653377 / 1000000 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    (699 / 1000) r (1301 / 1000)
    2 s (2385436 / 1000000) (653377 / 1000000)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

theorem shared_AL_corner
    (r s : ℝ)
    (hrlo : (699 / 1000 : ℝ) ≤ r)
    (hrhi : r ≤ 1301 / 1000)
    (hslo : (7 / 5 : ℝ) ≤ s)
    (hshi : s ≤ 2) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (328 / 1000 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    (699 / 1000) r (1301 / 1000)
    (7 / 5) s 2 (328 / 1000)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

theorem shared_HL_corner
    (r s : ℝ)
    (hrlo : (2 : ℝ) ≤ r)
    (hrhi : r ≤ 2385436 / 1000000)
    (hslo : (7 / 5 : ℝ) ≤ s)
    (hshi : s ≤ 2) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (601 / 1000 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    2 r (2385436 / 1000000)
    (7 / 5) s 2 (601 / 1000)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

theorem shared_AH_tight_corner
    (r s : ℝ)
    (hrlo : (27 / 25 : ℝ) ≤ r)
    (hrhi : r ≤ 1301 / 1000)
    (hslo : (2 : ℝ) ≤ s)
    (hshi : s ≤ 57 / 25) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (489 / 1000 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    (27 / 25) r (1301 / 1000)
    2 s (57 / 25) (489 / 1000)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

theorem shared_HL_tight_corner
    (r s : ℝ)
    (hrlo : (2 : ℝ) ≤ r)
    (hrhi : r ≤ 57 / 25)
    (hslo : (29 / 20 : ℝ) ≤ s)
    (hshi : s ≤ 2) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (5705 / 10000 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    2 r (57 / 25)
    (29 / 20) s 2 (5705 / 10000)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

theorem shared_AA_corner
    (r s : ℝ)
    (hrlo : (699 / 1000 : ℝ) ≤ r)
    (hrhi : r ≤ 1301 / 1000)
    (hslo : (699 / 1000 : ℝ) ≤ s)
    (hshi : s ≤ 1301 / 1000) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (-16 / 100 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    (699 / 1000) r (1301 / 1000)
    (699 / 1000) s (1301 / 1000) (-16 / 100)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

theorem shared_AH_angle_gt_49_2
    (x y : Plane) (g : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (2 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2385436 / 1000000)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    41 * Real.pi / 150 < g := by
  exact polar_pair_angle_gt_of_poly x y g (653377 / 1000000)
    (41 * Real.pi / 150) (by linarith) (by linarith) hsep
    (shared_AH_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos])
    cos_41pi_div_150_gt_653377ppm

theorem shared_AL_angle_gt_70_8
    (x y : Plane) (g : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    59 * Real.pi / 150 < g := by
  exact polar_pair_angle_gt_of_poly x y g (328 / 1000)
    (59 * Real.pi / 150) (by linarith) (by linarith) hsep
    (shared_AL_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos])
    cos_59pi_div_150_gt_328permille

theorem shared_HL_angle_gt_53
    (x y : Plane) (g : ℝ)
    (hxlo : (2 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 2385436 / 1000000)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    53 * Real.pi / 180 < g := by
  exact polar_pair_angle_gt_of_poly x y g (601 / 1000)
    (53 * Real.pi / 180) (by linarith) (by linarith) hsep
    (shared_HL_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos])
    cos_53pi_div_180_gt_601permille

theorem shared_AH_angle_gt_60_7
    (x y : Plane) (g : ℝ)
    (hxlo : (27 / 25 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (2 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 57 / 25)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    607 * Real.pi / 1800 < g := by
  exact polar_pair_angle_gt_of_poly x y g (489 / 1000)
    (607 * Real.pi / 1800) (by linarith) (by linarith) hsep
    (shared_AH_tight_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos])
    cos_607pi_div_1800_gt_489permille

theorem shared_HL_angle_gt_55_2
    (x y : Plane) (g : ℝ)
    (hxlo : (2 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 57 / 25)
    (hylo : (29 / 20 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    23 * Real.pi / 75 < g := by
  exact polar_pair_angle_gt_of_poly x y g (5705 / 10000)
    (23 * Real.pi / 75) (by linarith) (by linarith) hsep
    (shared_HL_tight_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos])
    cos_23pi_div_75_gt_5705ppm

theorem shared_AA_angle_gt_99
    (x y : Plane) (g : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (699 / 1000 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 1301 / 1000)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    11 * Real.pi / 20 < g := by
  exact polar_pair_angle_gt_of_poly x y g (-16 / 100)
    (11 * Real.pi / 20) (by linarith) (by linarith) hsep
    (shared_AA_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos])
    cos_11pi_div_20_gt_neg_16permille

theorem shared_LL_angle_ge_60
    (x y : Plane) (g : ℝ)
    (hxlo : (7 / 5 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 2)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    Real.pi / 3 ≤ g := by
  have hcorner (r s : ℝ)
      (hrlo : (7 / 5 : ℝ) ≤ r) (hrhi : r ≤ 2)
      (hslo : (7 / 5 : ℝ) ≤ s) (hshi : s ≤ 2) :
      pairExpr r s (1 / 2) ≤ 4 := by
    have hs := pairExpr_le_endpoint_max (7 / 5) s 2 r (1 / 2)
      hslo hshi
    rw [pairExpr_comm s r (1 / 2),
      pairExpr_comm (7 / 5) r (1 / 2),
      pairExpr_comm 2 r (1 / 2)] at hs
    have hla := pairExpr_le_endpoint_max (7 / 5) r 2
      (7 / 5) (1 / 2) hrlo hrhi
    have hlb := pairExpr_le_endpoint_max (7 / 5) r 2
      2 (1 / 2) hrlo hrhi
    have hcornerA : max (pairExpr (7 / 5) (7 / 5) (1 / 2))
        (pairExpr 2 (7 / 5) (1 / 2)) ≤ 4 := by
      norm_num [pairExpr]
    have hcornerB : max (pairExpr (7 / 5) 2 (1 / 2))
        (pairExpr 2 2 (1 / 2)) ≤ 4 := by
      norm_num [pairExpr]
    exact hs.trans (max_le
      (hla.trans hcornerA) (hlb.trans hcornerB))
  have hpoly := hcorner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi
  have hdist2 : 4 ≤ dist x y ^ 2 := by
    nlinarith [dist_nonneg (x := x) (y := y)]
  rw [dist_eq_norm, norm_sub_sq_real] at hdist2
  have hpolar := polar_inner x y
  rw [hcoslift] at hpolar
  have hcos : Real.cos g ≤ 1 / 2 := by
    dsimp [pairExpr] at hpoly
    nlinarith [mul_pos (by linarith : 0 < ‖x‖)
      (by linarith : 0 < ‖y‖)]
  by_contra hnot
  have hlt : g < Real.pi / 3 := lt_of_not_ge hnot
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi hg0
    (by nlinarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) hlt
  rw [Real.cos_pi_div_three] at hcoslt
  linarith

/-- The distinct-blocker class needs a bound between its two high centers.
The rational corner is valid on the full interval `[2, 2385436/10^6]`. -/
theorem distinct_HH_corner
    (r s : ℝ)
    (hrlo : (2 : ℝ) ≤ r)
    (hrhi : r ≤ 2385436 / 1000000)
    (hslo : (2 : ℝ) ≤ s)
    (hshi : s ≤ 2385436 / 1000000) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (653377 / 1000000 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    2 r (2385436 / 1000000)
    2 s (2385436 / 1000000) (653377 / 1000000)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

/-- Distinct high centers are separated angularly by more than 49.2 degrees. -/
theorem distinct_HH_angle_gt_49_2
    (x y : Plane) (g : ℝ)
    (hxlo : (2 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 2385436 / 1000000)
    (hylo : (2 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2385436 / 1000000)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    41 * Real.pi / 150 < g := by
  exact polar_pair_angle_gt_of_poly x y g (653377 / 1000000)
    (41 * Real.pi / 150) (by linarith) (by linarith) hsep
    (distinct_HH_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos])
    cos_41pi_div_150_gt_653377ppm

/-- A sharper low-low corner certifies the 100-degree cost used by the
finite cyclic word reduction. -/
theorem distinct_AA_corner
    (r s : ℝ)
    (hrlo : (699 / 1000 : ℝ) ≤ r)
    (hrhi : r ≤ 1301 / 1000)
    (hslo : (699 / 1000 : ℝ) ≤ s)
    (hshi : s ≤ 1301 / 1000) :
    r ^ 2 + s ^ 2 - 4 <
      2 * (-18 / 100 : ℝ) * r * s := by
  have h := pairExpr_lt_four_of_corners
    (699 / 1000) r (1301 / 1000)
    (699 / 1000) s (1301 / 1000) (-18 / 100)
    hrlo hrhi hslo hshi
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  dsimp [pairExpr] at h
  linarith

/-- Distinct non-outer centers in class A have angular separation greater
than 100 degrees on the entire radial cap rectangle. -/
theorem distinct_AA_angle_gt_100
    (x y : Plane) (g : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (699 / 1000 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 1301 / 1000)
    (hsep : 2 ≤ dist x y)
    (hcoslift : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi) :
    5 * Real.pi / 9 < g := by
  have hcos100 : (-18 / 100 : ℝ) < Real.cos (5 * Real.pi / 9) := by
    let l : ℝ := 5 * (3141592 / 1000000) / 18
    let u : ℝ := 5 * (3141593 / 1000000) / 18
    have hθ0 : (0 : ℝ) ≤ 5 * Real.pi / 9 := by positivity
    have hθ2 : 5 * Real.pi / 9 ≤ (2 : ℝ) := by
      nlinarith [Real.pi_lt_d6]
    have hl0 : 0 ≤ l := by dsimp [l]; norm_num
    have hlx : l ≤ (5 * Real.pi / 9) / 2 := by
      dsimp [l]
      nlinarith [Real.pi_gt_d6]
    have hxu : (5 * Real.pi / 9) / 2 ≤ u := by
      dsimp [u]
      nlinarith [Real.pi_lt_d6]
    have hu1 : u ≤ 1 := by dsimp [u]; norm_num
    exact cos_gt_of_half_interval (5 * Real.pi / 9) l u (-18 / 100)
      hθ0 hθ2 hl0 hlx hxu hu1 (by dsimp [l, u]; norm_num)
  exact polar_pair_angle_gt_of_poly x y g (-18 / 100)
    (5 * Real.pi / 9) (by linarith) (by linarith) hsep
    (distinct_AA_corner ‖x‖ ‖y‖ hxlo hxhi hylo hyhi)
    hcoslift hg0 hgpi (by positivity)
    (by nlinarith [Real.pi_pos]) hcos100

end CP15
