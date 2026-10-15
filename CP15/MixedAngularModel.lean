import CP15.DiscreteBoxCertificate
import CP15.RelativePolarOrder

namespace CP15

set_option maxHeartbeats 0

def mixedBinWord {n A Y : ℕ} (a : Fin A) (w : Fin n → Fin Y) : Fin (n + 1) → ℕ :=
  Fin.cases a.val (fun i => (w i).val)

def mixedBinExtra {n Y : ℕ} (extra : Fin Y → ℕ) (i : Fin (n + 1)) (k : ℕ) : ℕ :=
  if i = 0 then 0 else if h : k < Y then extra ⟨k, h⟩ else 0

def mixedBinPair {n A Y : ℕ} (ay : Fin A → Fin Y → ℕ) (yy : Fin Y → Fin Y → ℕ)
    (i _j : Fin (n + 1)) (a b : ℕ) : ℕ :=
  if i = 0 then
    if ha : a < A then if hb : b < Y then ay ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0
  else
    if ha : a < Y then if hb : b < Y then yy ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0

theorem mixedBinExtra_sum {n A Y : ℕ} (extra : Fin Y → ℕ)
    (a : Fin A) (w : Fin n → Fin Y) :
    (∑ i, mixedBinExtra extra i (mixedBinWord a w i)) = ∑ i, extra (w i) := by
  rw [Fin.sum_univ_succ]
  simp [mixedBinExtra, mixedBinWord, (w _).isLt]

/-- An actual minor-angle table supplies both directed inequalities,
including the wrapped gap. Equal lifted angles are retained. -/
theorem relative_pair_two_sided_bounds (x y : Plane) (a r s : ℝ) (k : ℕ)
    (hxr : polarLiftFrom a x = r) (hys : polarLiftFrom a y = s)
    (hr : a ≤ r) (hs : s ≤ a + 2 * Real.pi) (hrs : r ≤ s)
    (hlower : ∀ g : ℝ, Real.cos (polarArg x - polarArg y) = Real.cos g →
      0 ≤ g → (k : ℝ) / 10000 ≤ g) :
    (k : ℝ) ≤ 10000 * s - 10000 * r ∧
      (k : ℝ) ≤ 62832 - (10000 * s - 10000 * r) := by
  have hc : Real.cos (polarArg x - polarArg y) = Real.cos (r - s) := by
    rw [polarLiftFrom_cos a, hxr, hys]
  have hcdir : Real.cos (polarArg x - polarArg y) = Real.cos (s - r) := by
    rw [hc, ← Real.cos_neg (r - s)]
    congr 1
    ring
  have hcwrap : Real.cos (polarArg x - polarArg y) = Real.cos (r + 2 * Real.pi - s) := by
    rw [hc, show r + 2 * Real.pi - s = (r - s) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  have hd := hlower (s - r) hcdir (by linarith)
  have hw := hlower (r + 2 * Real.pi - s) hcwrap (by linarith)
  constructor <;> nlinarith [Real.pi_lt_d6]

/-- All-pair difference constraints of the actual ordered core/touching
family. Table lower bounds are the explicit premises of this generic
bridge and are independently proved when each concrete table is used. -/
theorem mixed_actual_angular_bounds {n A Y : ℕ}
    (core : Plane) (q : Fin n → Plane) (φ : Fin n → ℝ)
    (hmono : Monotone φ)
    (harg : ∀ i, polarLiftFrom (polarArg core) (q i) = φ i)
    (hrange : ∀ i, polarArg core ≤ φ i ∧ φ i ≤ polarArg core + 2 * Real.pi)
    (ay : Fin A → Fin Y → ℕ) (yy : Fin Y → Fin Y → ℕ)
    (a : Fin A) (w : Fin n → Fin Y)
    (hay : ∀ i g, Real.cos (polarArg core - polarArg (q i)) = Real.cos g →
      0 ≤ g → (ay a (w i) : ℝ) / 10000 ≤ g)
    (hyy : ∀ i j, i ≠ j → ∀ g,
      Real.cos (polarArg (q i) - polarArg (q j)) = Real.cos g →
      0 ≤ g → (yy (w i) (w j) : ℝ) / 10000 ≤ g) :
    Certificate.DiscreteAngularBounds (mixedBinPair ay yy) 62832 (mixedBinWord a w)
      (fun i => 10000 * Fin.cases (polarArg core) φ i) := by
  intro i
  refine Fin.cases ?_ (fun ii => ?_) i
  · intro j
    refine Fin.cases ?_ (fun jj => ?_) j
    · intro h
      exact False.elim (lt_irrefl _ h)
    · intro _h
      simpa [mixedBinPair, mixedBinWord, a.isLt, (w jj).isLt] using
        relative_pair_two_sided_bounds core (q jj) (polarArg core)
          (polarArg core) (φ jj) (ay a (w jj)) (polarLiftFrom_self core)
          (harg jj) le_rfl (hrange jj).2 (hrange jj).1 (hay jj)
  · intro j
    refine Fin.cases ?_ (fun jj => ?_) j
    · intro h
      have hn : ¬Fin.succ ii < (0 : Fin (n + 1)) := by simp
      exact False.elim (hn h)
    · intro h
      have hij : ii < jj := by simpa using h
      simpa [mixedBinPair, mixedBinWord, (w ii).isLt, (w jj).isLt] using
        relative_pair_two_sided_bounds (q ii) (q jj) (polarArg core)
          (φ ii) (φ jj) (yy (w ii) (w jj)) (harg ii) (harg jj)
          (hrange ii).1 (hrange jj).2 (hmono hij.le) (hyy ii jj hij.ne)

end CP15
