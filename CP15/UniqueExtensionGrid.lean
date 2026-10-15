import CP15.UniqueExtensionSeedCoordinates

namespace CP15

set_option maxHeartbeats 0
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

structure RationalRect where
  xlo : ℚ
  xhi : ℚ
  ylo : ℚ
  yhi : ℚ
  deriving DecidableEq, Repr

def RationalRect.Contains (b : RationalRect) (p : Plane) : Prop :=
  (b.xlo : ℝ) ≤ p 0 ∧ p 0 ≤ (b.xhi : ℝ) ∧
  (b.ylo : ℝ) ≤ p 1 ∧ p 1 ≤ (b.yhi : ℝ)

private theorem candidatePt_apply_zero (x y : ℝ) :
    Candidate.pt x y 0 = x := rfl

private theorem candidatePt_apply_one (x y : ℝ) :
    Candidate.pt x y 1 = y := rfl

/-- Coarse rational coordinate boxes for the fifteen exact candidate
centers at separation two. The bounds are deliberately wider than the
algebraic coordinates, leaving comfortable margins in the grid certificate. -/
def candidateSiteRect (i : Fin 15) : RationalRect :=
  match i.val with
  | 0 => ⟨-1, -1, -173 / 50, -83 / 25⟩
  | 1 => ⟨1, 1, -173 / 50, -83 / 25⟩
  | 2 => ⟨-73 / 25, -29 / 10, -21 / 10, -48 / 25⟩
  | 3 => ⟨29 / 10, 73 / 25, -21 / 10, -48 / 25⟩
  | 4 => ⟨-1, -1, -73 / 50, -33 / 25⟩
  | 5 => ⟨1, 1, -73 / 50, -33 / 25⟩
  | 6 => ⟨-89 / 25, -7 / 2, -9 / 50, -1 / 50⟩
  | 7 => ⟨7 / 2, 89 / 25, -9 / 50, -1 / 50⟩
  | 8 => ⟨-13 / 8, -8 / 5, 23 / 50, 29 / 50⟩
  | 9 => ⟨8 / 5, 13 / 8, 23 / 50, 29 / 50⟩
  | 10 => ⟨0, 0, 83 / 50, 87 / 50⟩
  | 11 => ⟨-113 / 40, -69 / 25, 103 / 50, 441 / 200⟩
  | 12 => ⟨69 / 25, 113 / 40, 103 / 50, 441 / 200⟩
  | 13 => ⟨-6 / 5, -29 / 25, 163 / 50, 673 / 200⟩
  | 14 => ⟨29 / 25, 6 / 5, 163 / 50, 673 / 200⟩
  | _ => ⟨0, 0, 0, 0⟩

theorem candidate_t_grid_bounds :
    (83 / 100 : ℝ) < Candidate.t ∧ Candidate.t < 87 / 100 := by
  rcases Candidate.simple_bounds with ⟨hslo, hsup, _, _, _, _, _, _⟩
  have hspos : 0 < 2 * Candidate.s := by positivity [Candidate.s_pos]
  constructor
  · unfold Candidate.t
    apply (lt_div_iff₀ hspos).2
    nlinarith
  · unfold Candidate.t
    apply (div_lt_iff₀ hspos).2
    nlinarith

/-- Each rational rectangle encloses the exact constructed center. -/
theorem candidateSiteRect_sound (i : Fin 15) :
    (candidateSiteRect i).Contains (Candidate.pointAtSeparationTwo i) := by
  rcases Candidate.simple_bounds with
    ⟨hslo, hsup, hclo, chigh, hulo, huhi, hvlo, hvhi⟩
  have ht := candidate_t_grid_bounds
  fin_cases i <;>
    simp only [RationalRect.Contains, candidateSiteRect,
      Candidate.pointAtSeparationTwo, Candidate.point,
      candidatePt_apply_zero, candidatePt_apply_one, PiLp.smul_apply,
      smul_eq_mul] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;>
    nlinarith [hslo, hsup, hclo, chigh, hulo, huhi, hvlo, hvhi,
      ht.1.le, ht.2.le]

def gridCoordLo (i : Fin 40) : ℚ := -4 + i.val / 5

def gridCoordHi (i : Fin 40) : ℚ := -4 + (i.val + 1) / 5

def gridCellRect (i j : Fin 40) : RationalRect :=
  ⟨gridCoordLo i, gridCoordHi i, gridCoordLo j, gridCoordHi j⟩

/-- Choose the one of the forty rational intervals containing a real
coordinate in `[-4,4]`. The final interval also contains the endpoint 4. -/
noncomputable def gridIndexFor (x : ℝ) : Fin 40 :=
  let f : ℕ := Int.toNat ⌊5 * (x + 4)⌋
  ⟨min f 39, by omega⟩

theorem grid_interval_covers_coordinate (x : ℝ)
    (hxlo : -4 ≤ x) (hxhi : x ≤ 4) :
    let i := gridIndexFor x
    (gridCoordLo i : ℝ) ≤ x ∧ x ≤ (gridCoordHi i : ℝ) := by
  let y : ℝ := 5 * (x + 4)
  let z : ℤ := ⌊y⌋
  let f : ℕ := Int.toNat z
  let m : ℕ := min f 39
  have hylo : 0 ≤ y := by dsimp [y]; nlinarith
  have hyhi : y ≤ 40 := by dsimp [y]; nlinarith
  have hzlo : 0 ≤ z := by
    rw [Int.floor_nonneg]
    exact hylo
  have hzfloorlo : (z : ℝ) ≤ y := by
    exact Int.floor_le y
  have hzfloorhi : y < (z : ℝ) + 1 := by
    exact Int.lt_floor_add_one y
  have hfcast : (f : ℝ) = (z : ℝ) := by
    dsimp [f]
    exact_mod_cast Int.toNat_of_nonneg hzlo
  have hfle : f ≤ 40 := by
    have h : (f : ℝ) ≤ 40 := by rw [hfcast]; linarith
    exact_mod_cast h
  have hmlo : (m : ℝ) ≤ y := by
    have hmf : m ≤ f := Nat.min_le_left f 39
    have hmf' : (m : ℝ) ≤ (f : ℝ) := by exact_mod_cast hmf
    rw [hfcast] at hmf'
    linarith
  have hmhi : y ≤ (m : ℝ) + 1 := by
    by_cases hf : f ≤ 39
    · have hm : m = f := Nat.min_eq_left hf
      rw [hm, hfcast]
      linarith
    · have hf40 : f = 40 := by omega
      have hz40 : (z : ℝ) = 40 := by rw [← hfcast, hf40]; norm_num
      have hy40 : y = 40 := by linarith
      have hm : m = 39 := Nat.min_eq_right (by omega)
      rw [hy40, hm]
      norm_num
  let i : Fin 40 := gridIndexFor x
  have hival : i.val = m := by
    simp [i, gridIndexFor, f, z, m, y]
  have hlo : (gridCoordLo i : ℝ) = -4 + (m : ℝ) / 5 := by
    simp [gridCoordLo, hival]
  have hhi : (gridCoordHi i : ℝ) = -4 + ((m : ℝ) + 1) / 5 := by
    simp [gridCoordHi, hival]
  change (gridCoordLo i : ℝ) ≤ x ∧ x ≤ (gridCoordHi i : ℝ)
  rw [hlo, hhi]
  constructor <;> dsimp [y] at hmlo hmhi <;> nlinarith

def maxAbsDiff (xlo xhi ylo yhi : ℚ) : ℚ :=
  max |xlo - yhi| |xhi - ylo|

def minAbsInterval (lo hi : ℚ) : ℚ :=
  if lo ≤ 0 ∧ 0 ≤ hi then 0 else min |lo| |hi|

def gridCellOutside (i j : Fin 40) : Prop :=
  minAbsInterval (gridCoordLo i) (gridCoordHi i) ^ 2 +
    minAbsInterval (gridCoordLo j) (gridCoordHi j) ^ 2 >
      (3522 / 1000 : ℚ) ^ 2

instance (i j : Fin 40) : Decidable (gridCellOutside i j) := by
  unfold gridCellOutside
  infer_instance

def gridCellLocal (i j : Fin 40) : Prop :=
  maxAbsDiff (gridCoordLo i) (gridCoordHi i)
      (candidateSiteRect 12).xlo (candidateSiteRect 12).xhi ^ 2 +
    maxAbsDiff (gridCoordLo j) (gridCoordHi j)
      (candidateSiteRect 12).ylo (candidateSiteRect 12).yhi ^ 2 ≤ 4

instance (i j : Fin 40) : Decidable (gridCellLocal i j) := by
  unfold gridCellLocal
  infer_instance

def gridCellBlockedBy (i j : Fin 40) (site : Fin 15) : Prop :=
  maxAbsDiff (gridCoordLo i) (gridCoordHi i)
      (candidateSiteRect site).xlo (candidateSiteRect site).xhi ^ 2 +
    maxAbsDiff (gridCoordLo j) (gridCoordHi j)
      (candidateSiteRect site).ylo (candidateSiteRect site).yhi ^ 2 < 4

instance (i j : Fin 40) (site : Fin 15) : Decidable (gridCellBlockedBy i j site) := by
  unfold gridCellBlockedBy
  infer_instance

private theorem plane_norm_sq_coordinates (p : Plane) :
    ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p

private theorem maxAbsDiff_controls_coordinate
    (xlo xhi ylo yhi : ℚ) (x y : ℝ)
    (hxlo : (xlo : ℝ) ≤ x) (hxhi : x ≤ (xhi : ℝ))
    (hylo : (ylo : ℝ) ≤ y) (hyhi : y ≤ (yhi : ℝ)) :
    |x - y| ≤ (maxAbsDiff xlo xhi ylo yhi : ℝ) := by
  have hrightQ : |xhi - ylo| ≤ max |xlo - yhi| |xhi - ylo| :=
    le_max_right _ _
  have hleftQ : |xlo - yhi| ≤ max |xlo - yhi| |xhi - ylo| :=
    le_max_left _ _
  have hright : |(xhi : ℝ) - ylo| ≤
      (maxAbsDiff xlo xhi ylo yhi : ℝ) := by exact_mod_cast hrightQ
  have hleft : |(xlo : ℝ) - yhi| ≤
      (maxAbsDiff xlo xhi ylo yhi : ℝ) := by exact_mod_cast hleftQ
  rw [abs_le]
  constructor
  · have hlowEndpoint : (xlo : ℝ) - yhi ≤ x - y := by linarith
    have hlow : -(maxAbsDiff xlo xhi ylo yhi : ℝ) ≤ (xlo : ℝ) - yhi := by
        calc
          -(maxAbsDiff xlo xhi ylo yhi : ℝ) ≤ -|(xlo : ℝ) - yhi| :=
            neg_le_neg hleft
        _ ≤ (xlo : ℝ) - yhi := by
          have h0 := le_abs_self ((yhi : ℝ) - xlo)
          have heq : (yhi : ℝ) - xlo = -((xlo : ℝ) - yhi) := by ring
          rw [heq, abs_neg] at h0
          linarith
    exact hlow.trans hlowEndpoint
  · have hupEndpoint : x - y ≤ (xhi : ℝ) - ylo := by linarith
    have hup : (xhi : ℝ) - ylo ≤ maxAbsDiff xlo xhi ylo yhi := by
      calc
        (xhi : ℝ) - ylo ≤ |(xhi : ℝ) - ylo| := le_abs_self _
        _ ≤ (maxAbsDiff xlo xhi ylo yhi : ℝ) := hright
    exact hupEndpoint.trans hup

private theorem maxAbsDiff_nonneg (xlo xhi ylo yhi : ℚ) :
    0 ≤ maxAbsDiff xlo xhi ylo yhi := by
  unfold maxAbsDiff
  exact (abs_nonneg _).trans (le_max_left _ _)

private theorem minAbsInterval_controls_abs
    (lo hi : ℚ) (x : ℝ)
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    0 ≤ (minAbsInterval lo hi : ℝ) ∧
      (minAbsInterval lo hi : ℝ) ≤ |x| := by
  have hle : lo ≤ hi := by exact_mod_cast (le_trans hxlo hxhi)
  unfold minAbsInterval
  split_ifs with hcross
  · norm_num
  · by_cases hlo : 0 ≤ lo
    · have hloR : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
      have hxnonneg : 0 ≤ x := hloR.trans hxlo
      have hmin : min |lo| |hi| ≤ lo := calc
        min |lo| |hi| ≤ |lo| := min_le_left _ _
        _ = lo := abs_of_nonneg hlo
      have hxabs : |x| = x := abs_of_nonneg hxnonneg
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ (lo : ℝ) := by
        exact_mod_cast hmin
      constructor
      · exact_mod_cast (show 0 ≤ min |lo| |hi| by positivity)
      · calc
          ((min |lo| |hi| : ℚ) : ℝ) ≤ (lo : ℝ) := hminR
          _ ≤ x := hxlo
          _ = |x| := hxabs.symm
    · have hloneg : lo < 0 := lt_of_not_ge hlo
      have hhineg : hi < 0 := by
        by_contra h
        have hhi0 : 0 ≤ hi := le_of_not_gt h
        exact hcross ⟨le_of_lt hloneg, hhi0⟩
      have hxnonpos : x ≤ 0 := le_trans hxhi (by exact_mod_cast hhineg.le)
      have hmin : min |lo| |hi| ≤ -hi := by
        have hhiQ : hi ≤ 0 := le_of_lt hhineg
        calc
          min |lo| |hi| ≤ |hi| := min_le_right _ _
          _ = -hi := abs_of_nonpos hhiQ
      have hxabs : |x| = -x := abs_of_nonpos hxnonpos
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ -(hi : ℝ) := by
        exact_mod_cast hmin
      constructor
      · exact_mod_cast (show 0 ≤ min |lo| |hi| by positivity)
      · calc
          ((min |lo| |hi| : ℚ) : ℝ) ≤ -(hi : ℝ) := hminR
          _ ≤ -x := by linarith
          _ = |x| := hxabs.symm

private theorem minAbsInterval_sq_le_of_mem
    (lo hi : ℚ) (x : ℝ)
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    (minAbsInterval lo hi : ℝ) ^ 2 ≤ x ^ 2 := by
  obtain ⟨hm0, hmx⟩ := minAbsInterval_controls_abs lo hi x hxlo hxhi
  have hprod := mul_nonneg (by linarith : 0 ≤ |x| - minAbsInterval lo hi)
    (by positivity : 0 ≤ |x| + minAbsInterval lo hi)
  nlinarith [sq_abs x]

theorem gridCellLocal_dist_le_two
    (i j : Fin 40) (x q : Plane)
    (hcell0 : (gridCoordLo i : ℝ) ≤ x 0 ∧ x 0 ≤ (gridCoordHi i : ℝ))
    (hcell1 : (gridCoordLo j : ℝ) ≤ x 1 ∧ x 1 ≤ (gridCoordHi j : ℝ))
    (hrect : (candidateSiteRect 12).Contains q)
    (hlocal : gridCellLocal i j) : dist x q ≤ 2 := by
  have hdx := maxAbsDiff_controls_coordinate
    (gridCoordLo i) (gridCoordHi i)
    (candidateSiteRect 12).xlo (candidateSiteRect 12).xhi
    (x 0) (q 0) hcell0.1 hcell0.2 hrect.1 hrect.2.1
  have hdy := maxAbsDiff_controls_coordinate
    (gridCoordLo j) (gridCoordHi j)
    (candidateSiteRect 12).ylo (candidateSiteRect 12).yhi
    (x 1) (q 1) hcell1.1 hcell1.2 hrect.2.2.1 hrect.2.2.2
  have hlocalR :
      (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect 12).xlo (candidateSiteRect 12).xhi : ℝ) ^ 2 +
      (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect 12).ylo (candidateSiteRect 12).yhi : ℝ) ^ 2 ≤ 4 := by
    exact_mod_cast hlocal
  have hMx : 0 ≤ (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
      (candidateSiteRect 12).xlo (candidateSiteRect 12).xhi : ℝ) := by
    exact_mod_cast maxAbsDiff_nonneg _ _ _ _
  have hMy : 0 ≤ (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
      (candidateSiteRect 12).ylo (candidateSiteRect 12).yhi : ℝ) := by
    exact_mod_cast maxAbsDiff_nonneg _ _ _ _
  have hdistSq : dist x q ^ 2 = (x 0 - q 0) ^ 2 + (x 1 - q 1) ^ 2 := by
    rw [dist_eq_norm_sub, plane_norm_sq_coordinates]
    simp [PiLp.sub_apply]
  have hdxSq : (x 0 - q 0) ^ 2 ≤
      (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect 12).xlo (candidateSiteRect 12).xhi : ℝ) ^ 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect 12).xlo (candidateSiteRect 12).xhi : ℝ) - |x 0 - q 0| by linarith)
      (show 0 ≤ (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect 12).xlo (candidateSiteRect 12).xhi : ℝ) + |x 0 - q 0| by
          linarith [hMx, abs_nonneg (x 0 - q 0)])
    nlinarith [sq_abs (x 0 - q 0), hprod]
  have hdySq : (x 1 - q 1) ^ 2 ≤
      (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect 12).ylo (candidateSiteRect 12).yhi : ℝ) ^ 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect 12).ylo (candidateSiteRect 12).yhi : ℝ) - |x 1 - q 1| by linarith)
      (show 0 ≤ (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect 12).ylo (candidateSiteRect 12).yhi : ℝ) + |x 1 - q 1| by
          linarith [hMy, abs_nonneg (x 1 - q 1)])
    nlinarith [sq_abs (x 1 - q 1), hprod]
  have hsq : dist x q ^ 2 ≤ 4 := by
    rw [hdistSq]
    exact (add_le_add hdxSq hdySq).trans hlocalR
  have hnonneg : 0 ≤ dist x q := dist_nonneg
  nlinarith [sq_nonneg (dist x q - 2)]

theorem gridCellBlockedBy_dist_lt_two
    (i j : Fin 40) (site : Fin 15) (x q : Plane)
    (hcell0 : (gridCoordLo i : ℝ) ≤ x 0 ∧ x 0 ≤ (gridCoordHi i : ℝ))
    (hcell1 : (gridCoordLo j : ℝ) ≤ x 1 ∧ x 1 ≤ (gridCoordHi j : ℝ))
    (hrect : (candidateSiteRect site).Contains q)
    (hblocked : gridCellBlockedBy i j site) : dist x q < 2 := by
  have hdx := maxAbsDiff_controls_coordinate
    (gridCoordLo i) (gridCoordHi i)
    (candidateSiteRect site).xlo (candidateSiteRect site).xhi
    (x 0) (q 0) hcell0.1 hcell0.2 hrect.1 hrect.2.1
  have hdy := maxAbsDiff_controls_coordinate
    (gridCoordLo j) (gridCoordHi j)
    (candidateSiteRect site).ylo (candidateSiteRect site).yhi
    (x 1) (q 1) hcell1.1 hcell1.2 hrect.2.2.1 hrect.2.2.2
  have hblockedR :
      (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect site).xlo (candidateSiteRect site).xhi : ℝ) ^ 2 +
      (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect site).ylo (candidateSiteRect site).yhi : ℝ) ^ 2 < 4 := by
    exact_mod_cast hblocked
  have hMx : 0 ≤ (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
      (candidateSiteRect site).xlo (candidateSiteRect site).xhi : ℝ) := by
    exact_mod_cast maxAbsDiff_nonneg _ _ _ _
  have hMy : 0 ≤ (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
      (candidateSiteRect site).ylo (candidateSiteRect site).yhi : ℝ) := by
    exact_mod_cast maxAbsDiff_nonneg _ _ _ _
  have hdistSq : dist x q ^ 2 = (x 0 - q 0) ^ 2 + (x 1 - q 1) ^ 2 := by
    rw [dist_eq_norm_sub, plane_norm_sq_coordinates]
    simp [PiLp.sub_apply]
  have hdxSq : (x 0 - q 0) ^ 2 ≤
      (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect site).xlo (candidateSiteRect site).xhi : ℝ) ^ 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect site).xlo (candidateSiteRect site).xhi : ℝ) - |x 0 - q 0| by linarith)
      (show 0 ≤ (maxAbsDiff (gridCoordLo i) (gridCoordHi i)
        (candidateSiteRect site).xlo (candidateSiteRect site).xhi : ℝ) + |x 0 - q 0| by
          linarith [hMx, abs_nonneg (x 0 - q 0)])
    nlinarith [sq_abs (x 0 - q 0), hprod]
  have hdySq : (x 1 - q 1) ^ 2 ≤
      (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect site).ylo (candidateSiteRect site).yhi : ℝ) ^ 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect site).ylo (candidateSiteRect site).yhi : ℝ) - |x 1 - q 1| by linarith)
      (show 0 ≤ (maxAbsDiff (gridCoordLo j) (gridCoordHi j)
        (candidateSiteRect site).ylo (candidateSiteRect site).yhi : ℝ) + |x 1 - q 1| by
          linarith [hMy, abs_nonneg (x 1 - q 1)])
    nlinarith [sq_abs (x 1 - q 1), hprod]
  have hsq : dist x q ^ 2 < 4 := by
    rw [hdistSq]
    exact (add_le_add hdxSq hdySq).trans_lt hblockedR
  have hnonneg : 0 ≤ dist x q := dist_nonneg
  nlinarith [sq_nonneg (dist x q - 2)]

def gridCellHasDisposition (i j : Fin 40) : Prop :=
  gridCellOutside i j ∨ gridCellLocal i j ∨
    ∃ site : Fin 15, site ≠ 12 ∧ gridCellBlockedBy i j site

macro "gridCellDispositionProof" : tactic => `(tactic| first
  | apply Or.inl
    norm_num [gridCellOutside, minAbsInterval, gridCoordLo, gridCoordHi]
    done
  | apply Or.inr
    apply Or.inl
    norm_num [gridCellLocal, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(0 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(1 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(2 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(3 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(4 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(5 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(6 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(7 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(8 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(9 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(10 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(11 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(13 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
  | apply Or.inr
    apply Or.inr
    refine ⟨(14 : Fin 15), ?_, ?_⟩
    · norm_num
    · norm_num [gridCellBlockedBy, maxAbsDiff, gridCoordLo, gridCoordHi, candidateSiteRect]
    done
)

private theorem gridCellHasDisposition_row_0 (j : Fin 40) :
    gridCellHasDisposition (0 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_1 (j : Fin 40) :
    gridCellHasDisposition (1 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_2 (j : Fin 40) :
    gridCellHasDisposition (2 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_3 (j : Fin 40) :
    gridCellHasDisposition (3 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_4 (j : Fin 40) :
    gridCellHasDisposition (4 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_5 (j : Fin 40) :
    gridCellHasDisposition (5 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_6 (j : Fin 40) :
    gridCellHasDisposition (6 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_7 (j : Fin 40) :
    gridCellHasDisposition (7 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_8 (j : Fin 40) :
    gridCellHasDisposition (8 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_9 (j : Fin 40) :
    gridCellHasDisposition (9 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_10 (j : Fin 40) :
    gridCellHasDisposition (10 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_11 (j : Fin 40) :
    gridCellHasDisposition (11 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_12 (j : Fin 40) :
    gridCellHasDisposition (12 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_13 (j : Fin 40) :
    gridCellHasDisposition (13 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_14 (j : Fin 40) :
    gridCellHasDisposition (14 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_15 (j : Fin 40) :
    gridCellHasDisposition (15 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_16 (j : Fin 40) :
    gridCellHasDisposition (16 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_17 (j : Fin 40) :
    gridCellHasDisposition (17 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_18 (j : Fin 40) :
    gridCellHasDisposition (18 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_19 (j : Fin 40) :
    gridCellHasDisposition (19 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_20 (j : Fin 40) :
    gridCellHasDisposition (20 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_21 (j : Fin 40) :
    gridCellHasDisposition (21 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_22 (j : Fin 40) :
    gridCellHasDisposition (22 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_23 (j : Fin 40) :
    gridCellHasDisposition (23 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_24 (j : Fin 40) :
    gridCellHasDisposition (24 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_25 (j : Fin 40) :
    gridCellHasDisposition (25 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_26 (j : Fin 40) :
    gridCellHasDisposition (26 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_27 (j : Fin 40) :
    gridCellHasDisposition (27 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_28 (j : Fin 40) :
    gridCellHasDisposition (28 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_29 (j : Fin 40) :
    gridCellHasDisposition (29 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_30 (j : Fin 40) :
    gridCellHasDisposition (30 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_31 (j : Fin 40) :
    gridCellHasDisposition (31 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_32 (j : Fin 40) :
    gridCellHasDisposition (32 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_33 (j : Fin 40) :
    gridCellHasDisposition (33 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_34 (j : Fin 40) :
    gridCellHasDisposition (34 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_35 (j : Fin 40) :
    gridCellHasDisposition (35 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_36 (j : Fin 40) :
    gridCellHasDisposition (36 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_37 (j : Fin 40) :
    gridCellHasDisposition (37 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_38 (j : Fin 40) :
    gridCellHasDisposition (38 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

private theorem gridCellHasDisposition_row_39 (j : Fin 40) :
    gridCellHasDisposition (39 : Fin 40) j := by
  fin_cases j
  all_goals
    dsimp [gridCellHasDisposition]
    gridCellDispositionProof

theorem gridCellHasDisposition_all (i j : Fin 40) :
    gridCellHasDisposition i j := by
  fin_cases i
  all_goals
    first
    | exact gridCellHasDisposition_row_0 j
    | exact gridCellHasDisposition_row_1 j
    | exact gridCellHasDisposition_row_2 j
    | exact gridCellHasDisposition_row_3 j
    | exact gridCellHasDisposition_row_4 j
    | exact gridCellHasDisposition_row_5 j
    | exact gridCellHasDisposition_row_6 j
    | exact gridCellHasDisposition_row_7 j
    | exact gridCellHasDisposition_row_8 j
    | exact gridCellHasDisposition_row_9 j
    | exact gridCellHasDisposition_row_10 j
    | exact gridCellHasDisposition_row_11 j
    | exact gridCellHasDisposition_row_12 j
    | exact gridCellHasDisposition_row_13 j
    | exact gridCellHasDisposition_row_14 j
    | exact gridCellHasDisposition_row_15 j
    | exact gridCellHasDisposition_row_16 j
    | exact gridCellHasDisposition_row_17 j
    | exact gridCellHasDisposition_row_18 j
    | exact gridCellHasDisposition_row_19 j
    | exact gridCellHasDisposition_row_20 j
    | exact gridCellHasDisposition_row_21 j
    | exact gridCellHasDisposition_row_22 j
    | exact gridCellHasDisposition_row_23 j
    | exact gridCellHasDisposition_row_24 j
    | exact gridCellHasDisposition_row_25 j
    | exact gridCellHasDisposition_row_26 j
    | exact gridCellHasDisposition_row_27 j
    | exact gridCellHasDisposition_row_28 j
    | exact gridCellHasDisposition_row_29 j
    | exact gridCellHasDisposition_row_30 j
    | exact gridCellHasDisposition_row_31 j
    | exact gridCellHasDisposition_row_32 j
    | exact gridCellHasDisposition_row_33 j
    | exact gridCellHasDisposition_row_34 j
    | exact gridCellHasDisposition_row_35 j
    | exact gridCellHasDisposition_row_36 j
    | exact gridCellHasDisposition_row_37 j
    | exact gridCellHasDisposition_row_38 j
    | exact gridCellHasDisposition_row_39 j


/-- Every feasible point separated from the other fourteen candidate
centers is forced to be candidate center 12. The proof uses the checked
40 by 40 rational grid certificate and the exact local seed inequality. -/
theorem candidate_point12_unique_from_grid
    (x : Plane)
    (hdisk : ‖x‖ ≤ candidateB)
    (hsep : ∀ j : Fin 15, j ≠ 12 → 2 ≤ dist x (Candidate.pointAtSeparationTwo j)) :
    x = Candidate.pointAtSeparationTwo 12 := by
  have hB : candidateB < (3522 / 1000 : ℝ) := by
    linarith [candidateB_local_bounds.2]
  have hcoord (k : Fin 2) : -4 ≤ x k ∧ x k ≤ 4 := by
    have hnk : ‖x k‖ ≤ ‖x‖ := PiLp.norm_apply_le x k
    rw [Real.norm_eq_abs] at hnk
    have hbound : |x k| ≤ 4 := by linarith
    exact abs_le.mp hbound
  let i := gridIndexFor (x 0)
  let j := gridIndexFor (x 1)
  have hcell0 := grid_interval_covers_coordinate (x 0)
    (hcoord 0).1 (hcoord 0).2
  have hcell1 := grid_interval_covers_coordinate (x 1)
    (hcoord 1).1 (hcoord 1).2
  have hdisp := gridCellHasDisposition_all i j
  have hrect12 := candidateSiteRect_sound (12 : Fin 15)
  rcases hdisp with hout | hrest
  · have hmin0 := minAbsInterval_sq_le_of_mem
      (gridCoordLo i) (gridCoordHi i) (x 0) hcell0.1 hcell0.2
    have hmin1 := minAbsInterval_sq_le_of_mem
      (gridCoordLo j) (gridCoordHi j) (x 1) hcell1.1 hcell1.2
    have houtR :
        (minAbsInterval (gridCoordLo i) (gridCoordHi i) : ℝ) ^ 2 +
          (minAbsInterval (gridCoordLo j) (gridCoordHi j) : ℝ) ^ 2 >
          (3522 / 1000 : ℝ) ^ 2 := by
      unfold gridCellOutside at hout
      have hcast :
          ((minAbsInterval (gridCoordLo i) (gridCoordHi i) ^ 2 +
            minAbsInterval (gridCoordLo j) (gridCoordHi j) ^ 2 : ℚ) : ℝ) >
          (((3522 / 1000 : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hout
      have hsumcast :
          ((minAbsInterval (gridCoordLo i) (gridCoordHi i) ^ 2 +
            minAbsInterval (gridCoordLo j) (gridCoordHi j) ^ 2 : ℚ) : ℝ) =
          (minAbsInterval (gridCoordLo i) (gridCoordHi i) : ℝ) ^ 2 +
            (minAbsInterval (gridCoordLo j) (gridCoordHi j) : ℝ) ^ 2 := by simp
      have hradcast : (((3522 / 1000 : ℚ) ^ 2 : ℚ) : ℝ) =
          (3522 / 1000 : ℝ) ^ 2 := by simp
      rw [← hsumcast, ← hradcast]
      exact hcast
    have hnormSq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 :=
      plane_norm_sq_coordinates x
    have hnormLower : (3522 / 1000 : ℝ) ^ 2 < ‖x‖ ^ 2 := by
      rw [hnormSq]
      nlinarith
    have hnormUpper : ‖x‖ ^ 2 < (3522 / 1000 : ℝ) ^ 2 := by
      have hdiff : 0 < (3522 / 1000 : ℝ) - ‖x‖ := by linarith
      have hsum : 0 < (3522 / 1000 : ℝ) + ‖x‖ := by positivity
      have hprod := mul_pos hdiff hsum
      nlinarith
    linarith
  · rcases hrest with hlocal | ⟨site, hsite, hblocked⟩
    · have hnear := gridCellLocal_dist_le_two i j x
        (Candidate.pointAtSeparationTwo 12) hcell0 hcell1 hrect12 hlocal
      have hinner := hsep 9 (by norm_num)
      have houter := hsep 14 (by norm_num)
      exact candidate_point12_unique_if_near x hnear hinner houter hdisk
    · have hrect := candidateSiteRect_sound site
      have hclose := gridCellBlockedBy_dist_lt_two i j site x
        (Candidate.pointAtSeparationTwo site) hcell0 hcell1 hrect hblocked
      have hfar := hsep site hsite
      linarith

end CP15
