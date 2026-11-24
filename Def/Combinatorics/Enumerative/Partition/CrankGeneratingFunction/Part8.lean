module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/
namespace MetaMathlibExt

namespace CrankNonneg

noncomputable def crkPsiFun (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) : Nat.Partition L :=
  crkMkPartition L (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν))
    (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
    (fun x hx => by
      have hbig2 := (crk_psi_index k L hk ν hν).2
      have hge := crk_psi_ge_two k _ _ hk (crk_nonOne_sorted ν)
        (crk_nonOne_ge_two ν) hbig2 x hx
      omega)
    (by
      have hbig2 := (crk_psi_index k L hk ν hν).2
      have hsum : psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)
          + (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)).sum
          = Multiset.count 1 ν.parts + (nonOneParts ν).sum :=
        crk_psi_sum _ _ (crk_nonOne_ge_two ν)
      have hωsum := crk_omega_add_sum ν
      omega)

end CrankNonneg
end MetaMathlibExt
