import CP15.SixPoint
import CP15.ParametricOuterGap

open scoped Topology

namespace CP15

theorem elementary_sin_pi_div_ten :
    Real.sin (Real.pi / 10) = (Real.sqrt 5 - 1) / 4 := by
  have h5sq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h5n := Real.sqrt_nonneg 5
  have h5lo : 1 < Real.sqrt 5 := by nlinarith
  have hs : 0 ≤ Real.sin (Real.pi / 10) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos])
  have hc := Real.cos_two_mul (Real.pi / 10)
  rw [show 2 * (Real.pi / 10) = Real.pi / 5 by ring,
    Real.cos_pi_div_five] at hc
  have hsc := Real.sin_sq_add_cos_sq (Real.pi / 10)
  have hsq : Real.sin (Real.pi / 10) ^ 2 =
      ((Real.sqrt 5 - 1) / 4) ^ 2 := by nlinarith
  exact (sq_eq_sq₀ hs (by linarith : 0 ≤ (Real.sqrt 5 - 1) / 4)).mp hsq

/-- Below `1+sqrt 5`, ten separated boundary centers are impossible.
A slightly larger threshold than `pi/5` avoids any loss of strictness
when summing the boundary gaps. -/
theorem boundary_count_le_nine_below_elementary_radius
    (p : Fin 15 → Plane) (b : ℝ) (hb : 0 < b)
    (hbC : b < 1 + Real.sqrt 5) (hsep : Separated p 2) :
    (boundarySet p b).card ≤ 9 := by
  have hspos : 0 < Real.sin (Real.pi / 10) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hprod : (1 + Real.sqrt 5) * Real.sin (Real.pi / 10) = 1 := by
    rw [elementary_sin_pi_div_ten]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have hsmall : b * Real.sin (Real.pi / 10) < 1 := by
    simpa [hprod] using mul_lt_mul_of_pos_right hbC hspos
  have hcontinuous : Continuous (fun t : ℝ =>
      b * Real.sin ((Real.pi / 5 + t) / 2)) := by fun_prop
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
      b * Real.sin ((Real.pi / 5 + t) / 2) < 1 := by
    have htend := hcontinuous.tendsto 0
    have h0 : b * Real.sin ((Real.pi / 5 + (0 : ℝ)) / 2) < 1 := by
      convert hsmall using 1 <;> congr 1 <;> ring
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htend.eventually (eventually_lt_nhds h0))
  have hθevent : ∀ᶠ t : ℝ in 𝓝[>] 0, Real.pi / 5 + t < Real.pi := by
    have htend : Filter.Tendsto (fun t : ℝ => Real.pi / 5 + t)
        (𝓝 0) (𝓝 (Real.pi / 5)) := by
      have hc : Continuous (fun t : ℝ => Real.pi / 5 + t) := by fun_prop
      simpa using hc.tendsto 0
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htend.eventually (eventually_lt_nhds (by nlinarith [Real.pi_pos])))
  have hchoose : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < t ∧ b * Real.sin ((Real.pi / 5 + t) / 2) < 1 ∧
        Real.pi / 5 + t < Real.pi := by
    filter_upwards [self_mem_nhdsWithin, hevent, hθevent] with t ht hs hθ
    exact ⟨ht, hs, hθ⟩
  obtain ⟨t, ht, hbsmall, hθpi⟩ := hchoose.exists
  let θ := Real.pi / 5 + t
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  by_contra hnot
  have hK10 : 10 ≤ (boundarySet p b).card := by omega
  have hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => every_next_gap_ge_threshold p b θ hb hθ0 hθpi.le hbsmall hsep hsize i)
  rw [sum_next_boundary_gaps p b hsize] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, boundaryAngles_card p b hsep] at hsum
  have hKReal : (10 : ℝ) ≤ (boundarySet p b).card := by exact_mod_cast hK10
  dsimp [θ] at hsum hθ0
  nlinarith

/-- An elementary, independent lower bound for every feasible fifteen-point
packing at separation two. The representative is selected at the same
radius; no smaller-N packing theorem is an input. -/
theorem centerFeasible_radius_ge_one_add_sqrt_five {b : ℝ}
    (hfeas : CenterFeasible 15 b) : 1 + Real.sqrt 5 ≤ b := by
  classical
  have hb : 2 < b := centerFeasible_radius_gt_two hfeas
  have hbpos : 0 < b := by linarith
  by_contra hnot
  have hbC : b < 1 + Real.sqrt 5 := lt_of_not_ge hnot
  obtain ⟨p, hp, hsep, hK, hD⟩ := exists_maxBoundaryCount_with_inner_cap hb hfeas
  have hK9 := boundary_count_le_nine_below_elementary_radius p b hbpos hbC hsep
  have h5sq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h5n := Real.sqrt_nonneg 5
  have hfactor : 0 < (1 + Real.sqrt 5 - b) * (b + Real.sqrt 5 - 1) :=
    mul_pos (by linarith) (by nlinarith)
  have hpoly : b ^ 2 - 2 * b < 4 := by nlinarith
  have hD2 : D b < 2 := by
    have hdiv : b - 2 < 4 / b := (lt_div_iff₀ hbpos).2 (by nlinarith)
    unfold D
    linarith
  let I := Finset.univ \ boundarySet p b
  have hIcard : 6 ≤ I.card := by
    dsimp [I]
    rw [Finset.card_sdiff_of_subset (by simp), Finset.card_univ]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 6) ≤ I.card by simpa using hIcard)
  have hinner (i : Fin 6) : ‖p (e i)‖ < b := by
    have hi := he ⟨i, rfl⟩
    have hne : ‖p (e i)‖ ≠ b := by simpa [I, boundarySet] using hi
    exact lt_of_le_of_ne (hp (e i)) hne
  exact six_point_open_two_obstruction (fun i => p (e i))
    (fun i j hij => hsep (e i) (e j) (e.injective.ne hij))
    (fun i => (hD (e i) (hinner i)).trans hD2)

end CP15
