import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbitNesting
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalTransfers_eq_of_union_eq_sameMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitNesting.lean)
-/
@[path]
private lemma canonicalTransfers_eq_of_union_eq_sameMask_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hunion : canonicalTransferUnion ends m k zero c.1.1 = canonicalTransferUnion ends m k zero d.1.1) :
-- imply
  canonicalMiddleTransfer ends m c.1.1 k zero = canonicalMiddleTransfer ends m d.1.1 k zero ∧ canonicalOuterTransfer ends m c.1.1 k zero = canonicalOuterTransfer ends m d.1.1 k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransfers_eq_of_union_eq_sameMask hloop hjk hkl c d hunion

/--
[canonicalTransferUnion_subset_of_adjacentComponentNesting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitNesting.lean)
-/
@[path]
private lemma canonicalTransferUnion_subset_of_adjacentComponentNesting_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hnest : CanonicalMaskAdjacentComponentNesting ends m j k l zero p)
  (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d)
  (hgood : RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m r.1.1 k zero) (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1) k zero)
  (hbad : ¬ RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m r.1.1 k zero) (canonicalOuterTransfer ends m r.1.1 k zero) d.1.1) k zero) :
-- imply
  canonicalTransferUnion ends m k zero d.1.1 ⊆ canonicalTransferUnion ends m k zero r.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferUnion_subset_of_adjacentComponentNesting ends m j k l zero p hnest r c d hcd hgood hbad

/--
[canonicalMaskAdjacentStrictDescent_of_componentNesting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitNesting.lean)
-/
@[path]
private lemma canonicalMaskAdjacentStrictDescent_of_componentNesting_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hnest : CanonicalMaskAdjacentComponentNesting ends m j k l zero p) :
-- imply
  CanonicalMaskAdjacentStrictDescent ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskAdjacentStrictDescent_of_componentNesting ends m j k l zero hloop hjk hkl hk0 p hnest

/--
[GrahamFiberMinor_of_canonicalMaskAdjacentComponentNesting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitNesting.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskAdjacentComponentNesting_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hnest : ∀ p : Finset I × Finset I, CanonicalMaskAdjacentComponentNesting ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskAdjacentComponentNesting ends m j k l zero hloop hjk hkl hk0 hnest


-- created on 2026-10-23
