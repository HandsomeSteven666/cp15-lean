import CP15.BlockerCapacity

open scoped InnerProductSpace

namespace CP15

/-- Oriented area in the two-dimensional center plane. -/
def planeCross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

private theorem plane_dot_coords (u v : Plane) :
    ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two]
  ring

private theorem plane_norm_sq_coords (u : Plane) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq u

/-- The two-dimensional dot/cross decomposition. -/
theorem plane_dot_cross_identity (y u v : Plane) :
    ‖y‖ ^ 2 * ⟪u, v⟫_ℝ =
      ⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ + planeCross y u * planeCross y v := by
  rw [plane_norm_sq_coords, plane_dot_coords,
    plane_dot_coords, plane_dot_coords]
  simp [planeCross]
  ring

private theorem planeCross_sub_self (y x : Plane) :
    planeCross y (x - y) = planeCross y x := by
  simp [planeCross, PiLp.sub_apply]
  ring

/-- Two separated strict contact targets of a blocker of radius below
`12/5` lie on opposite sides of its radial line. -/
theorem strict_shared_contacts_cross_negative
    (x z y : Plane)
    (hy : ‖y‖ < 12 / 5)
    (hxy : dist x y = 2) (hzy : dist z y = 2)
    (hblockx : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hblockz : ‖z‖ ^ 2 < ⟪y, z⟫_ℝ)
    (hxz : 2 ≤ dist x z) :
    planeCross y x * planeCross y z < 0 := by
  let a := x - y
  let c := z - y
  have hd₀ : ⟪y, a⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four x y hxy hblockx
  have hd₁ : ⟪y, c⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four z y hzy hblockz
  have hp : ⟪a, c⟫_ℝ ≤ 2 :=
    contact_vector_pair_inner_le_two x z y hxy hzy hxz
  have hnorm : 0 ≤ ‖y‖ := norm_nonneg y
  have hysq : ‖y‖ ^ 2 < (12 / 5 : ℝ) ^ 2 := by nlinarith
  have hdprod : 16 < ⟪y, a⟫_ℝ * ⟪y, c⟫_ℝ := by
    have h₀ : 0 < -4 - ⟪y, a⟫_ℝ := by linarith
    have h₁ : 0 < -4 - ⟪y, c⟫_ℝ := by linarith
    nlinarith [mul_pos h₀ h₁]
  have hscaled : ‖y‖ ^ 2 * ⟪a, c⟫_ℝ < 16 := by
    have := mul_le_mul_of_nonneg_left hp (sq_nonneg ‖y‖)
    nlinarith
  have hidentity := plane_dot_cross_identity y a c
  rw [planeCross_sub_self, planeCross_sub_self] at hidentity
  nlinarith

private theorem one_of_opposite_cross_products_nonnegative
    (a c w : ℝ) (hac : a * c < 0) :
    0 ≤ w * a ∨ 0 ≤ w * c := by
  by_cases hwa : 0 ≤ w * a
  · exact Or.inl hwa
  · right
    have hwalt : w * a < 0 := lt_of_not_ge hwa
    rcases lt_trichotomy w 0 with hwneg | hwzero | hwpos
    · have ha : 0 < a := by
        by_contra hnot
        have hnonpos : a ≤ 0 := le_of_not_gt hnot
        exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hwneg.le
          hnonpos)) hwalt
      have hc : c < 0 := by
        by_contra hnot
        have hnonneg : 0 ≤ c := le_of_not_gt hnot
        exact (not_lt_of_ge (mul_nonneg ha.le hnonneg)) hac
      exact (mul_pos_of_neg_of_neg hwneg hc).le
    · subst w
      norm_num at hwalt
    · have ha : a < 0 := by
        by_contra hnot
        have hnonneg : 0 ≤ a := le_of_not_gt hnot
        exact (not_lt_of_ge (mul_nonneg hwpos.le hnonneg)) hwalt
      have hc : 0 < c := by
        by_contra hnot
        have hnonpos : c ≤ 0 := le_of_not_gt hnot
        exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos ha.le
          hnonpos)) hac
      exact (mul_pos hwpos hc).le

private theorem small_third_point_hits_contact
    (w x y : Plane) (s : ℝ)
    (hs : ‖y‖ = s) (hslo : 2 < s) (hshi : s < 12 / 5)
    (hxy : dist x y = 2)
    (hblock : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hside : 0 ≤ planeCross y w * planeCross y x)
    (hw : ‖w‖ ≤ 8 / s - s) : dist w x < 2 := by
  let r := ‖w‖
  let t := s - 4 / s
  let R := 8 / s - s
  have hspos : 0 < s := by linarith
  have htpos : 0 < t := by
    dsimp [t]
    have : 4 / s < s := by
      apply (div_lt_iff₀ hspos).2
      nlinarith
    linarith
  have hRpos : 0 < R := by
    dsimp [R]
    apply sub_pos.mpr
    apply (lt_div_iff₀ hspos).2
    nlinarith
  have htr : s * t = s ^ 2 - 4 := by
    dsimp [t]
    field_simp
  have hRr : s * R = 8 - s ^ 2 := by
    dsimp [R]
    field_simp
  have hcorner : R ^ 2 + s ^ 2 - 4 + 2 * R * t = 4 := by
    dsimp [R, t]
    field_simp
    ring
  have hr0 : 0 ≤ r := norm_nonneg w
  have hrR : r ≤ R := hw
  have hsqcontact : ‖x - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hxy]
    norm_num
  have ha : ‖x - y‖ = 2 := by
    rw [← dist_eq_norm, hxy]
  have hdotya : ⟪y, x - y⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four x y hxy hblock
  have hx_sq : ‖x‖ ^ 2 < s ^ 2 - 4 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hs] at hdotya
    rw [norm_sub_sq_real, hs] at hsqcontact
    nlinarith [real_inner_comm x y]
  have hdotyx_upper : ⟪y, x⟫_ℝ < s * t := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hs] at hdotya
    nlinarith [htr]
  have hdotyx_pos : 0 < ⟪y, x⟫_ℝ := by
    have hcs := abs_real_inner_le_norm y (x - y)
    rw [hs, ha] at hcs
    have hneg := neg_le_abs (⟪y, x - y⟫_ℝ)
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hs] at hneg
    nlinarith [hcs]
  have hdotyw_lower : -s * r ≤ ⟪y, w⟫_ℝ := by
    have hcs := abs_real_inner_le_norm y w
    rw [hs] at hcs
    have hneg := neg_le_abs (⟪y, w⟫_ℝ)
    dsimp [r]
    linarith
  have hdotwx_lower : -r * t ≤ ⟪w, x⟫_ℝ := by
    have hidentity := plane_dot_cross_identity y w x
    rw [hs] at hidentity
    have hprodlo := mul_le_mul_of_nonneg_right hdotyw_lower
      hdotyx_pos.le
    have hprodbound := mul_le_mul_of_nonpos_left hdotyx_upper.le
      (by nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by linarith) hr0] :
        -s * r ≤ 0)
    nlinarith [sq_pos_of_pos hspos]
  have hdist_sq : dist w x ^ 2 = r ^ 2 + ‖x‖ ^ 2 - 2 * ⟪w, x⟫_ℝ := by
    rw [dist_eq_norm, norm_sub_sq_real]
    dsimp [r]
    ring
  have hradial : r ^ 2 + 2 * r * t ≤ R ^ 2 + 2 * R * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (add_nonneg hr0 hRpos.le)]
  have hdistlt : dist w x ^ 2 < 4 := by
    rw [hdist_sq]
    linarith
  have hdnonneg : 0 ≤ dist w x := dist_nonneg
  nlinarith

/-- A third center separated from two targets of one strict radial blocker
has radius greater than `8/s-s`. This is a purely algebraic two-dimensional
form of the shared-blocker midpoint bound. -/
theorem third_radius_gt_eight_div_sub_of_shared_strict_blocker
    (x z w y : Plane)
    (hslo : 2 < ‖y‖) (hshi : ‖y‖ < 12 / 5)
    (hxy : dist x y = 2) (hzy : dist z y = 2)
    (hblockx : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hblockz : ‖z‖ ^ 2 < ⟪y, z⟫_ℝ)
    (hxz : 2 ≤ dist x z)
    (hwx : 2 ≤ dist w x) (hwz : 2 ≤ dist w z) :
    8 / ‖y‖ - ‖y‖ < ‖w‖ := by
  by_contra hnot
  have hwsmall : ‖w‖ ≤ 8 / ‖y‖ - ‖y‖ := le_of_not_gt hnot
  have hcross := strict_shared_contacts_cross_negative x z y hshi
    hxy hzy hblockx hblockz hxz
  rcases one_of_opposite_cross_products_nonnegative
      (planeCross y x) (planeCross y z) (planeCross y w) hcross with
    hside | hside
  · have hdist := small_third_point_hits_contact w x y ‖y‖ rfl
      hslo hshi hxy hblockx hside hwsmall
    linarith
  · have hdist := small_third_point_hits_contact w z y ‖y‖ rfl
      hslo hshi hzy hblockz hside hwsmall
    linarith

/-- The third target of a selected two-plus-one blocker family imposes a
correlated lower bound on the radius of its own strict blocker. -/
theorem selected_shared_pair_third_radius_and_blocker_sq
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (target blocker : Fin 3 → Fin 15)
    (hinj : Function.Injective target)
    (hdata : ∀ c, ‖p (blocker c)‖ < b ∧
      2 < ‖p (blocker c)‖ ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (target c)‖ ^ 2 <
        ⟪p (blocker c), p (target c)⟫_ℝ)
    (c d e : Fin 3) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) (hsame : blocker c = blocker d) :
    8 / ‖p (blocker c)‖ - ‖p (blocker c)‖ < ‖p (target e)‖ ∧
    4 + (8 / ‖p (blocker c)‖ - ‖p (blocker c)‖) ^ 2 <
      ‖p (blocker e)‖ ^ 2 := by
  have hyhi : ‖p (blocker c)‖ < 12 / 5 :=
    (hD _ (hdata c).1).trans
      (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)
  have hdc : dist (p (target d)) (p (blocker c)) = 2 := by
    simpa [← hsame] using (hdata d).2.2.1
  have hsc : ‖p (target d)‖ ^ 2 <
      ⟪p (blocker c), p (target d)⟫_ℝ := by
    simpa [← hsame] using (hdata d).2.2.2
  have htarget :
      8 / ‖p (blocker c)‖ - ‖p (blocker c)‖ < ‖p (target e)‖ :=
    third_radius_gt_eight_div_sub_of_shared_strict_blocker
      (p (target c)) (p (target d)) (p (target e)) (p (blocker c))
      (hdata c).2.1 hyhi (hdata c).2.2.1 hdc
      (hdata c).2.2.2 hsc
      (hsep _ _ (fun h => hcd (hinj h)))
      (hsep _ _ (fun h => hce (hinj h.symm)))
      (hsep _ _ (fun h => hde (hinj h.symm)))
  have hblocksq := blocker_radius_sq (p (target e)) (p (blocker e))
    (hdata e).2.2.1 (hdata e).2.2.2
  have hRpos : 0 < 8 / ‖p (blocker c)‖ - ‖p (blocker c)‖ := by
    have hspos : 0 < ‖p (blocker c)‖ := by linarith [(hdata c).2.1]
    apply sub_pos.mpr
    apply (lt_div_iff₀ hspos).2
    nlinarith
  constructor
  · exact htarget
  · nlinarith [norm_nonneg (p (target e))]

end CP15
