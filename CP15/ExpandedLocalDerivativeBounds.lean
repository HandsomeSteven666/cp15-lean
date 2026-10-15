import CP15.ContactAngleDerivative
import CP15.CandidateBounds

namespace CP15

set_option maxHeartbeats 0

private theorem sq_interval (x l u : ℝ) (hl0 : 0 ≤ l) (hl : l ≤ x) (hu : x ≤ u) :
    l ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ u ^ 2 := by
  constructor <;> nlinarith

private theorem quotient_lower (num den lo nlo d2hi : ℝ)
    (hden : 0 < den) (hlo : 0 ≤ lo) (hnlo : 0 ≤ nlo)
    (hn : nlo ≤ num) (hd2 : den ^ 2 ≤ d2hi)
    (hcert : lo ^ 2 * d2hi < nlo ^ 2) : lo < num / den := by
  have hn2 : nlo ^ 2 ≤ num ^ 2 := by nlinarith
  have hd := mul_le_mul_of_nonneg_left hd2 (sq_nonneg lo)
  have hs : (lo * den) ^ 2 < num ^ 2 := by nlinarith
  have hloD := mul_nonneg hlo hden.le
  apply (lt_div_iff₀ hden).2
  nlinarith

private theorem quotient_upper (num den hi nhi d2lo : ℝ)
    (hden : 0 < den) (hhi : 0 ≤ hi) (hn0 : 0 ≤ num)
    (hn : num ≤ nhi) (hd2 : d2lo ≤ den ^ 2)
    (hcert : nhi ^ 2 < hi ^ 2 * d2lo) : num / den < hi := by
  have hn2 : num ^ 2 ≤ nhi ^ 2 := by nlinarith
  have hd := mul_le_mul_of_nonneg_left hd2 (sq_nonneg hi)
  have hs : num ^ 2 < (hi * den) ^ 2 := by nlinarith
  have hhiD := mul_nonneg hhi hden.le
  apply (div_lt_iff₀ hden).2
  nlinarith

/-- The paper's strict outer-contact derivative enclosure, proved for the
whole closed rational local box. The denominator is checked positive. -/
theorem expanded_outer_derivative_bounds (b r : ℝ)
    (hblo : (35213 / 10000 : ℝ) ≤ b) (hbhi : b ≤ 35214 / 10000)
    (hrlo : (42 / 25 : ℝ) ≤ r) (hrhi : r ≤ 43 / 25) :
    0 < contactRadicand b r ∧
      (73 / 100 : ℝ) < contactAngleDerivative b r ∧
      contactAngleDerivative b r < 89 / 100 := by
  let l : ℝ := 42 / 25
  let u : ℝ := 43 / 25
  let bl : ℝ := 35213 / 10000
  let bu : ℝ := 35214 / 10000
  let fmin : ℝ := 4 - (bu - l) ^ 2
  let fmax : ℝ := 4 - (bl - u) ^ 2
  let gmin : ℝ := (bl + l) ^ 2 - 4
  let gmax : ℝ := (bu + u) ^ 2 - 4
  let nmin : ℝ := bl ^ 2 - u ^ 2 - 4
  let nmax : ℝ := bu ^ 2 - l ^ 2 - 4
  have hbsq := sq_interval b bl bu (by dsimp [bl]; norm_num) hblo hbhi
  have hrsq := sq_interval r l u (by dsimp [l]; norm_num) hrlo hrhi
  have hdiff := sq_interval (b - r) (bl - u) (bu - l)
    (by dsimp [bl, u]; norm_num) (by dsimp [bl, u]; linarith)
    (by dsimp [bu, l]; linarith)
  have hsum := sq_interval (b + r) (bl + l) (bu + u)
    (by dsimp [bl, l]; norm_num) (by dsimp [bl, l]; linarith)
    (by dsimp [bu, u]; linarith)
  have hf : fmin ≤ 4 - (b - r) ^ 2 ∧ 4 - (b - r) ^ 2 ≤ fmax := by
    dsimp [fmin, fmax]; constructor <;> linarith
  have hg : gmin ≤ (b + r) ^ 2 - 4 ∧ (b + r) ^ 2 - 4 ≤ gmax := by
    dsimp [gmin, gmax]; constructor <;> linarith
  have hf0 : 0 < fmin := by dsimp [fmin, bu, l]; norm_num
  have hg0 : 0 < gmin := by dsimp [gmin, bl, l]; norm_num
  have hHlo : fmin * gmin ≤ contactRadicand b r :=
    mul_le_mul hf.1 hg.1 hg0.le ((hf0.trans_le hf.1).le)
  have hHhi : contactRadicand b r ≤ fmax * gmax :=
    mul_le_mul hf.2 hg.2 (hg0.trans_le hg.1).le ((hf0.trans_le (hf.1.trans hf.2)).le)
  have hHpos : 0 < contactRadicand b r := (mul_pos hf0 hg0).trans_le hHlo
  have hr0 : 0 < r := by linarith
  have hden : 0 < r * Real.sqrt (contactRadicand b r) :=
    mul_pos hr0 (Real.sqrt_pos.mpr hHpos)
  have hd2 : (r * Real.sqrt (contactRadicand b r)) ^ 2 =
      r ^ 2 * contactRadicand b r := by rw [mul_pow, Real.sq_sqrt hHpos.le]
  have hdlo : l ^ 2 * (fmin * gmin) ≤
      (r * Real.sqrt (contactRadicand b r)) ^ 2 := by
    rw [hd2]
    exact mul_le_mul hrsq.1 hHlo (by positivity) (sq_nonneg r)
  have hdhi : (r * Real.sqrt (contactRadicand b r)) ^ 2 ≤
      u ^ 2 * (fmax * gmax) := by
    rw [hd2]
    exact mul_le_mul hrsq.2 hHhi hHpos.le (sq_nonneg u)
  have hn : nmin ≤ b ^ 2 - r ^ 2 - 4 ∧ b ^ 2 - r ^ 2 - 4 ≤ nmax := by
    dsimp [nmin, nmax]; constructor <;> linarith
  have hn0 : 0 ≤ nmin := by dsimp [nmin, bl, u]; norm_num
  refine ⟨hHpos, ?_, ?_⟩
  · exact quotient_lower _ _ _ nmin _ hden (by norm_num) hn0 hn.1 hdhi
      (by dsimp [nmin, bl, u, fmax, gmax, bu, l]; norm_num)
  · exact quotient_upper _ _ _ nmax _ hden (by norm_num) (hn0.trans hn.1) hn.2 hdlo
      (by dsimp [nmax, bu, l, fmin, gmin, bl, u]; norm_num)

/-- The inner-pair partial derivative is strictly negative throughout the
same local square, with magnitude between 0.35 and 0.51. -/
theorem expanded_inner_negative_derivative_bounds (r s : ℝ)
    (hrlo : (42 / 25 : ℝ) ≤ r) (hrhi : r ≤ 43 / 25)
    (hslo : (42 / 25 : ℝ) ≤ s) (hshi : s ≤ 43 / 25) :
    0 < contactRadicand s r ∧
      (35 / 100 : ℝ) < -contactAngleDerivative s r ∧
      -contactAngleDerivative s r < 51 / 100 := by
  let l : ℝ := 42 / 25
  let u : ℝ := 43 / 25
  let Hmin : ℝ := (4 - (u - l) ^ 2) * ((2 * l) ^ 2 - 4)
  let Hmax : ℝ := 4 * ((2 * u) ^ 2 - 4)
  let nmin : ℝ := 4 + l ^ 2 - u ^ 2
  let nmax : ℝ := 4 + u ^ 2 - l ^ 2
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hrsq := sq_interval r l u (by dsimp [l]; norm_num) hrlo hrhi
  have hssq := sq_interval s l u (by dsimp [l]; norm_num) hslo hshi
  have hdiff : (s - r) ^ 2 ≤ (u - l) ^ 2 := by
    have hu : 0 ≤ u - l := by dsimp [u, l]; norm_num
    have h1 : s - r ≤ u - l := by dsimp [u, l]; linarith
    have h2 : -(u - l) ≤ s - r := by dsimp [u, l]; linarith
    nlinarith
  have hsum := sq_interval (s + r) (2 * l) (2 * u)
    (by dsimp [l]; norm_num) (by dsimp [l]; linarith) (by dsimp [u]; linarith)
  have hflo : 4 - (u - l) ^ 2 ≤ 4 - (s - r) ^ 2 := by linarith
  have hfhi : 4 - (s - r) ^ 2 ≤ 4 := by nlinarith [sq_nonneg (s - r)]
  have hglo : (2 * l) ^ 2 - 4 ≤ (s + r) ^ 2 - 4 := by linarith
  have hghi : (s + r) ^ 2 - 4 ≤ (2 * u) ^ 2 - 4 := by linarith
  have hf0 : 0 < 4 - (u - l) ^ 2 := by dsimp [u, l]; norm_num
  have hg0 : 0 < (2 * l) ^ 2 - 4 := by dsimp [l]; norm_num
  have hHlo : Hmin ≤ contactRadicand s r :=
    mul_le_mul hflo hglo hg0.le (hf0.trans_le hflo).le
  have hHhi : contactRadicand s r ≤ Hmax :=
    mul_le_mul hfhi hghi (hg0.trans_le hglo).le (by norm_num)
  have hHmin0 : 0 < Hmin := mul_pos hf0 hg0
  have hHpos : 0 < contactRadicand s r := hHmin0.trans_le hHlo
  have hden : 0 < r * Real.sqrt (contactRadicand s r) :=
    mul_pos hr0 (Real.sqrt_pos.mpr hHpos)
  have hd2 : (r * Real.sqrt (contactRadicand s r)) ^ 2 =
      r ^ 2 * contactRadicand s r := by rw [mul_pow, Real.sq_sqrt hHpos.le]
  have hdlo : l ^ 2 * Hmin ≤ (r * Real.sqrt (contactRadicand s r)) ^ 2 := by
    rw [hd2]; exact mul_le_mul hrsq.1 hHlo hHmin0.le (sq_nonneg r)
  have hdhi : (r * Real.sqrt (contactRadicand s r)) ^ 2 ≤ u ^ 2 * Hmax := by
    rw [hd2]; exact mul_le_mul hrsq.2 hHhi hHpos.le (sq_nonneg u)
  have hn : nmin ≤ r ^ 2 - s ^ 2 + 4 ∧ r ^ 2 - s ^ 2 + 4 ≤ nmax := by
    dsimp [nmin, nmax]; constructor <;> linarith
  have hn0 : 0 ≤ nmin := by dsimp [nmin, l, u]; norm_num
  have heq : -contactAngleDerivative s r =
      (r ^ 2 - s ^ 2 + 4) / (r * Real.sqrt (contactRadicand s r)) := by
    unfold contactAngleDerivative
    rw [← neg_div]
    congr 1
    ring
  rw [heq]
  refine ⟨hHpos, ?_, ?_⟩
  · exact quotient_lower _ _ _ nmin _ hden (by norm_num) hn0 hn.1 hdhi
      (by dsimp [nmin, l, u, Hmax]; norm_num)
  · exact quotient_upper _ _ _ nmax _ hden (by norm_num) (hn0.trans hn.1) hn.2 hdlo
      (by dsimp [nmax, l, u, Hmin]; norm_num)

end CP15
