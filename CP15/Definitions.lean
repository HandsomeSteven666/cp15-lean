import Mathlib

/-!
The original point-packing problem, expressed as a predicate on a candidate
separation rather than as a supremum.  This keeps existence and optimality
logically separate until compactness is formalized.
-/

namespace CP15

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def InUnitDisk {n : ℕ} (p : Fin n → Plane) : Prop :=
  ∀ i, ‖p i‖ ≤ 1

def Separated {n : ℕ} (p : Fin n → Plane) (d : ℝ) : Prop :=
  ∀ i j, i ≠ j → d ≤ dist (p i) (p j)

def PointFeasible (n : ℕ) (d : ℝ) : Prop :=
  ∃ p : Fin n → Plane, InUnitDisk p ∧ Separated p d

def PointOptimal (n : ℕ) (d : ℝ) : Prop :=
  PointFeasible n d ∧ ∀ e : ℝ, PointFeasible n e → e ≤ d

def InDisk {n : ℕ} (b : ℝ) (p : Fin n → Plane) : Prop :=
  ∀ i, ‖p i‖ ≤ b

def CenterFeasible (n : ℕ) (b : ℝ) : Prop :=
  ∃ p : Fin n → Plane, InDisk b p ∧ Separated p 2

def CenterOptimal (n : ℕ) (b : ℝ) : Prop :=
  CenterFeasible n b ∧ ∀ c : ℝ, CenterFeasible n c → b ≤ c

end CP15
