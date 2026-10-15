import CP15.RationalPairAngle

namespace CP15

set_option maxHeartbeats 0

/-- Complete closed core-radius cover with exact four-corner checks. -/
theorem distinct_case_i_AH_AL_sum_gt_131 (x y z : Plane) (g h : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖) (hxhi : ‖x‖ ≤ (1301 / 1000 : ℝ))
    (hylo : (2 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ (23 / 10 : ℝ))
    (hzlo : (3 / 2 : ℝ) ≤ ‖z‖) (hzhi : ‖z‖ ≤ (2 : ℝ))
    (hsepY : 2 ≤ dist x y) (hsepZ : 2 ≤ dist x z)
    (hcosY : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hcosZ : Real.cos (polarArg x - polarArg z) = Real.cos h)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) :
    (131 : ℝ) * Real.pi / 180 < g + h := by
  by_cases hcell0 : ‖x‖ ≤ (1 : ℝ)
  ·
    exact coupled_pair_box_angle_sum_gt x y z g h
      (131 : ℝ) (699 / 1000 : ℝ) (1 : ℝ) (2 : ℝ) (23 / 10 : ℝ) (3 / 2 : ℝ) (2 : ℝ) (5641 / 100 : ℝ) (7549 / 100 : ℝ) (553151 / 1000000 : ℝ) (250001 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) hylo hyhi hzlo hzhi
      hsepY hsepZ hcosY hcosZ hg0 hh0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num)
  ·
    exact coupled_pair_box_angle_sum_gt x y z g h
      (131 : ℝ) (1 : ℝ) (1301 / 1000 : ℝ) (2 : ℝ) (23 / 10 : ℝ) (3 / 2 : ℝ) (2 : ℝ) (30049 / 500 : ℝ) (17749 / 250 : ℝ) (24919 / 50000 : ℝ) (325251 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) hylo hyhi hzlo hzhi
      hsepY hsepZ hcosY hcosZ hg0 hh0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num)

/-- Complete closed core-radius cover with exact four-corner checks. -/
theorem distinct_case_i_two_AH_sum_gt_115_8 (x y z : Plane) (g h : ℝ)
    (hxlo : (1 : ℝ) ≤ ‖x‖) (hxhi : ‖x‖ ≤ (1301 / 1000 : ℝ))
    (hylo : (2 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ (23 / 10 : ℝ))
    (hzlo : (2 : ℝ) ≤ ‖z‖) (hzhi : ‖z‖ ≤ (596359 / 250000 : ℝ))
    (hsepY : 2 ≤ dist x y) (hsepZ : 2 ≤ dist x z)
    (hcosY : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hcosZ : Real.cos (polarArg x - polarArg z) = Real.cos h)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) :
    (579 / 5 : ℝ) * Real.pi / 180 < g + h := by
  by_cases hcell0 : ‖x‖ ≤ (2301 / 2000 : ℝ)
  ·
    exact coupled_pair_box_angle_sum_gt x y z g h
      (579 / 5 : ℝ) (1 : ℝ) (2301 / 2000 : ℝ) (2 : ℝ) (23 / 10 : ℝ) (2 : ℝ) (596359 / 250000 : ℝ) (30067 / 500 : ℝ) (55667 / 1000 : ℝ) (497827 / 1000000 : ℝ) (563903 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) hylo hyhi hzlo hzhi
      hsepY hsepZ hcosY hcosZ hg0 hh0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num)
  ·
    exact coupled_pair_box_angle_sum_gt x y z g h
      (579 / 5 : ℝ) (2301 / 2000 : ℝ) (1301 / 1000 : ℝ) (2 : ℝ) (23 / 10 : ℝ) (2 : ℝ) (596359 / 250000 : ℝ) (30049 / 500 : ℝ) (56687 / 1000 : ℝ) (24919 / 50000 : ℝ) (274551 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) hylo hyhi hzlo hzhi
      hsepY hsepZ hcosY hcosZ hg0 hh0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num); norm_num)
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num)

end CP15
