import CP15.FinitePathCertificate

namespace CP15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/- Exact integer data. Every directed bin word is quantified over below;
no representative or externally asserted successful check is imported. -/

def k9BinLo (i : Fin 7) : ℚ := ![123 / 100, 3 / 2, 33 / 20, 9 / 5, 39 / 20, 21 / 10, 9 / 4] i
def k9BinHi (i : Fin 7) : ℚ := ![3 / 2, 33 / 20, 9 / 5, 39 / 20, 21 / 10, 9 / 4, 4771 / 2000] i
def k9GammaUnits (i : Fin 7) : ℕ := ![0, 0, 2937, 4072, 4766, 5233, 5555] i
def k9ExtraUnits (i : Fin 7) : ℕ := ![0, 0, 115, 2385, 3773, 4707, 5351] i
def k9PairUnits (i j : Fin 7) : ℕ :=
  ![![14593, 13730, 12912, 12122, 11348, 10578, 9876], ![13730, 13021, 12340, 11675, 11017, 10358, 9756], ![12912, 12340, 11780, 11225, 10669, 10108, 9592], ![12122, 11675, 11225, 10769, 10305, 9831, 9391], ![11348, 11017, 10669, 10305, 9926, 9531, 9161], ![10578, 10358, 10108, 9831, 9531, 9211, 8904], ![9876, 9756, 9592, 9391, 9161, 8904, 8651]] i j
def k9PairCosBound (i j : Fin 7) : ℚ :=
  ![![1388889 / 12500000, 3929293 / 20000000, 27592593 / 100000000, 35085471 / 100000000, 42222223 / 100000000, 1962963 / 4000000, 55063373 / 100000000], ![3929293 / 20000000, 26538109 / 100000000, 33038721 / 100000000, 1961927 / 5000000, 45202021 / 100000000, 50976431 / 100000000, 7007473 / 12500000], ![27592593 / 100000000, 33038721 / 100000000, 7654321 / 20000000, 5417557 / 12500000, 6035053 / 12500000, 13279321 / 25000000, 28707063 / 50000000], ![35085471 / 100000000, 1961927 / 5000000, 5417557 / 12500000, 1896121 / 4000000, 51434677 / 100000000, 13860399 / 25000000, 59043799 / 100000000], ![42222223 / 100000000, 45202021 / 100000000, 6035053 / 12500000, 51434677 / 100000000, 54648527 / 100000000, 57910053 / 100000000, 60889803 / 100000000], ![1962963 / 4000000, 50976431 / 100000000, 13279321 / 25000000, 13860399 / 25000000, 57910053 / 100000000, 15123457 / 25000000, 31454437 / 50000000], ![55063373 / 100000000, 7007473 / 12500000, 28707063 / 50000000, 59043799 / 100000000, 60889803 / 100000000, 31454437 / 50000000, 12970877 / 20000000]] i j

def k9Alphabet : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- Exhaust all possible first bins and all five remaining letters.
The checked pruning criterion has nonnegative integer increments. -/
theorem k9_path_check (first : Fin 7) :
    Certificate.pathCheck k9Alphabet k9ExtraUnits k9PairUnits 11010 62832 first
      5 first (k9ExtraUnits first) 0 = true := by
  fin_cases first <;> decide +kernel

/-- The full 7^6 word domain follows from the proved checker semantics,
including every direction and every cyclic wrap edge. -/
theorem k9_six_bin_word_excluded :
    ∀ w : Fin 6 → Fin 7,
      11010 < ∑ i, k9ExtraUnits (w i) ∨
        62832 < ∑ i, k9PairUnits (w i) (w (i + 1)) := by
  intro w
  have hs := Certificate.pathCheck_sound k9Alphabet k9ExtraUnits k9PairUnits
    11010 62832 (w 0) 5 (w 0) (k9ExtraUnits (w 0)) 0 (k9_path_check (w 0))
    [w 1, w 2, w 3, w 4, w 5] (by rfl)
    (fun x _ => by fin_cases x <;> simp [k9Alphabet])
  simpa [Certificate.pathCost, Fin.sum_univ_succ, Nat.add_assoc] using hs

end CP15
