/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part42
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagPlaneConfig_recurrence
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hparity : Even (n - k)) :
    (n + 1 - k) * Nat.card (ZagPlaneConfig n hn k) =
      (∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.card (ZagPlaneConfig n hn (k + 2 * (d.val + 1)))) +
        (n - 1).factorial * Nat.stirlingFirst n k := by
  have hpair := zagCard_originalTotal_add_reflectedTotal n k hn
  have horiginal := zagCard_originalTotal_eq_sum_depth n k 1 hn
  have hreflected := zagCard_reflectedTotal_eq_sum_depth n k hn
  have hdecompose := zagCard_planeConfigDiagonal_decompose n k hn hparity
  have htotal := zagCard_planeConfigDiagonal n k hn
  have hswap : Nat.card (ZagPlaneConfig n hn k) =
      Nat.card (ZagPlaneConfigBy n hn 1 k) :=
    Nat.card_congr (zagReflectConfigEquiv n hn k 1)
  have hreflected_add :
      Nat.card (ZagReflectedTotal n hn k) +
          Nat.card (ZagPlaneConfig n hn k) =
        (n - 1).factorial * Nat.stirlingFirst n k := by
    calc
      _ = (∑ d : Fin n,
            Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k)) +
          Nat.card (ZagPlaneConfig n hn k) := by rw [hreflected]
      _ = Nat.card (ZagPlaneConfigBy n hn 1 k) +
          ∑ d : Fin n,
            Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k) := by
        rw [← hswap]
        exact Nat.add_comm _ _
      _ = Nat.card (ZagPlaneConfigDiagonal n hn k) := hdecompose.symm
      _ = (n - 1).factorial * Nat.stirlingFirst n k := htotal
  have hchoose (d : Fin n) :
      (k + 2 * (d.val + 1)).choose (2 * d.val + 3) =
        (k + 2 * (d.val + 1)).choose (k - 1) := by
    have hsum : k + 2 * (d.val + 1) =
        (2 * d.val + 3) + (k - 1) := by omega
    calc
      _ = ((2 * d.val + 3) + (k - 1)).choose (2 * d.val + 3) := by rw [hsum]
      _ = ((2 * d.val + 3) + (k - 1)).choose (k - 1) := Nat.choose_symm_add
      _ = (k + 2 * (d.val + 1)).choose (k - 1) := by rw [hsum]
  simp_rw [hchoose] at horiginal
  have hcoefficient : n + 1 - k = (n - k) + 1 := by omega
  calc
    (n + 1 - k) * Nat.card (ZagPlaneConfig n hn k) =
        (n - k) * Nat.card (ZagPlaneConfig n hn k) +
          Nat.card (ZagPlaneConfig n hn k) := by
      rw [hcoefficient, add_mul, one_mul]
    _ = (Nat.card (ZagOriginalTotal n hn k 1) +
          Nat.card (ZagReflectedTotal n hn k)) +
        Nat.card (ZagPlaneConfig n hn k) := by rw [hpair]
    _ = Nat.card (ZagOriginalTotal n hn k 1) +
        (Nat.card (ZagReflectedTotal n hn k) +
          Nat.card (ZagPlaneConfig n hn k)) := Nat.add_assoc _ _ _
    _ = Nat.card (ZagOriginalTotal n hn k 1) +
        (n - 1).factorial * Nat.stirlingFirst n k := by rw [hreflected_add]
    _ = (∑ d : Fin n,
          (k + 2 * (d.val + 1)).choose (k - 1) *
            Nat.card (ZagPlaneConfig n hn (k + 2 * (d.val + 1)))) +
        (n - 1).factorial * Nat.stirlingFirst n k := by rw [horiginal]

end MetaMathlibExt
