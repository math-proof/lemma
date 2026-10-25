/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedLucas.lean -/


import Def.NumberTheory.GeneralizedLucas
import Lemma.Nat.GeneralizedLucas
open Finset


/-- `k = 2` lower index `0` is `2` (classical Lucas start). -/
example : Nat.kGeneralizedLucas 2 (by omega) 0 (by omega) = 2 :=
  Nat.kGeneralizedLucas_zero 2 (by omega) _

/-- `k = 2` value at `1` is `1`. -/
example : Nat.kGeneralizedLucas 2 (by omega) 1 (by omega) = 1 :=
  Nat.kGeneralizedLucas_one 2 (by omega) _

/-- `k = 2` first recurrence instance at `n = 2`, i.e. `L_2 = L_1 + L_0`. -/
example : Nat.kGeneralizedLucas 2 (by omega) 2 (by omega) =
    ∑ i : Fin 2,
      Nat.kGeneralizedLucas 2 (by omega) ((2 : ℤ) - ((2 : ℕ) : ℤ) + (i.val : ℤ))
        (by omega) :=
  Nat.kGeneralizedLucas_recurrence 2 (by omega) (2 : ℤ) (by omega) (by omega)

/-- `k = 2` first recurrence value `L_2 = 3` (direct executable proof). -/
example : Nat.kGeneralizedLucas 2 (by omega) 2 (by omega) = 3 := by
  have hrecProof : 2 - ((2 : ℕ) : ℤ) ≤ (2 : ℤ) := by omega
  have hrec := Nat.kGeneralizedLucas_recurrence 2 (by omega) (2 : ℤ) (by omega) hrecProof
  have hbridge : Nat.kGeneralizedLucas 2 (by omega) 2 (by omega) =
      Nat.kGeneralizedLucas 2 (by omega) 2 hrecProof := rfl
  rw [hbridge, hrec, Fin.sum_univ_two]
  change Nat.kGeneralizedLucas 2 (by omega) 0 (by omega) +
      Nat.kGeneralizedLucas 2 (by omega) 1 (by omega) = 3
  calc Nat.kGeneralizedLucas 2 (by omega) 0 (by omega) +
        Nat.kGeneralizedLucas 2 (by omega) 1 (by omega)
      = 2 + 1 := by
        congr 1
        · exact Nat.kGeneralizedLucas_zero 2 (by omega) (by omega)
        · exact Nat.kGeneralizedLucas_one 2 (by omega) (by omega)
    _ = 3 := rfl

/-- `k = 3` lower index `-1` is `0`. -/
example : Nat.kGeneralizedLucas 3 (by omega) (-1) (by omega) = 0 :=
  Nat.kGeneralizedLucas_neg_eq_zero 3 (by omega) _ (by omega) (by omega)

/-- `k = 3` lowest index `2 - 3` via the lower lemma. -/
example : Nat.kGeneralizedLucas 3 (by omega) (2 - ((3 : ℕ) : ℤ)) (by omega) = 0 :=
  Nat.kGeneralizedLucas_lower_zero 3 (by omega) _

/-- `k = 3` value at `0` is `2`. -/
example : Nat.kGeneralizedLucas 3 (by omega) 0 (by omega) = 2 :=
  Nat.kGeneralizedLucas_zero 3 (by omega) _

/-- `k = 3` value at `1` is `1`. -/
example : Nat.kGeneralizedLucas 3 (by omega) 1 (by omega) = 1 :=
  Nat.kGeneralizedLucas_one 3 (by omega) _

/-- `k = 3` first recurrence instance at `n = 2`, i.e. `L_2 = L_1 + L_0 + L_{-1}`. -/
example : Nat.kGeneralizedLucas 3 (by omega) 2 (by omega) =
    ∑ i : Fin 3,
      Nat.kGeneralizedLucas 3 (by omega) ((2 : ℤ) - ((3 : ℕ) : ℤ) + (i.val : ℤ))
        (by omega) :=
  Nat.kGeneralizedLucas_recurrence 3 (by omega) (2 : ℤ) (by omega) (by omega)

/-- `k = 3` first recurrence value `L_2 = 3` (direct executable proof). -/
example : Nat.kGeneralizedLucas 3 (by omega) 2 (by omega) = 3 := by
  have hrecProof : 2 - ((3 : ℕ) : ℤ) ≤ (2 : ℤ) := by omega
  have hrec := Nat.kGeneralizedLucas_recurrence 3 (by omega) (2 : ℤ) (by omega) hrecProof
  have hbridge : Nat.kGeneralizedLucas 3 (by omega) 2 (by omega) =
      Nat.kGeneralizedLucas 3 (by omega) 2 hrecProof := rfl
  rw [hbridge, hrec, Fin.sum_univ_three]
  change Nat.kGeneralizedLucas 3 (by omega) (-1) (by omega) +
        Nat.kGeneralizedLucas 3 (by omega) 0 (by omega) +
        Nat.kGeneralizedLucas 3 (by omega) 1 (by omega) = 3
  calc Nat.kGeneralizedLucas 3 (by omega) (-1) (by omega) +
          Nat.kGeneralizedLucas 3 (by omega) 0 (by omega) +
          Nat.kGeneralizedLucas 3 (by omega) 1 (by omega)
      = (0 + 2) + 1 := by
        congr 1
        · congr 1
          · exact Nat.kGeneralizedLucas_neg_eq_zero 3 (by omega) (-1) (by omega)
              (by omega)
          · exact Nat.kGeneralizedLucas_zero 3 (by omega) (by omega)
        · exact Nat.kGeneralizedLucas_one 3 (by omega) (by omega)
    _ = 3 := rfl

