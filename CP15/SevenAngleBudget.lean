import CP15.M3K8

namespace CP15

/-- Rational lower cost for one adjacent pair among three low-radius and
four high-radius inner directions. `Fin 7` addition is cyclic. -/
def sevenAngleWeight (color : Fin 7 → Bool) (i : Fin 7) : ℚ :=
  if color i then
    if color (i + 1) then 3 / 2 else 181 / 200
  else if color (i + 1) then 181 / 200 else 171 / 200

/-- Exhaustive 128-word finite check. Exactly three of the seven positions
are low-radius. Every coloring has total rational cost at least `1257/200`.
The quantifier is over the full `Fin 7 → Bool` type, so no orbit or word is
omitted. -/
theorem sevenAngleWeight_sum_ge :
    ∀ color : Fin 7 → Bool,
      (Finset.univ.filter (fun i => color i)).card = 3 →
      (1257 / 200 : ℚ) ≤ ∑ i : Fin 7, sevenAngleWeight color i := by
  decide +kernel

/-- In the relevant radial annulus, two separated centers cannot have
the same polar argument. This lets the seven selected directions be sorted
without identifying distinct labels. -/
theorem seven_polarArg_injective
    (q : Fin 7 → Plane) (hsep : Separated q 2)
    (hrlo : ∀ i, (4 / 5 : ℝ) ≤ ‖q i‖)
    (hrhi : ∀ i, ‖q i‖ ≤ 14909 / 6250) :
    Function.Injective (fun i => polarArg (q i)) := by
  intro i j harg
  by_contra hij
  have hd := hsep i j hij
  have hd2 : 4 ≤ dist (q i) (q j) ^ 2 := by
    nlinarith [dist_nonneg (x := q i) (y := q j)]
  rw [dist_eq_norm, norm_sub_sq_real] at hd2
  have hdot := polar_inner (q i) (q j)
  change polarArg (q i) = polarArg (q j) at harg
  rw [harg, sub_self, Real.cos_zero] at hdot
  have hloi := hrlo i
  have hloj := hrlo j
  have hhii := hrhi i
  have hhij := hrhi j
  nlinarith

end CP15
