import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbitPropagation
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalMaskOrbitMinimumReference_disconnects_of_adjacentStrictDescent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitPropagation.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_disconnects_of_adjacentStrictDescent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hlocal : CanonicalMaskAdjacentStrictDescent ends m j k l zero p) :
-- imply
  RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m (canonicalMaskOrbitMinimumReference ends m j k l zero p d).1.1 k zero) (canonicalOuterTransfer ends m (canonicalMaskOrbitMinimumReference ends m j k l zero p d).1.1 k zero) d.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_disconnects_of_adjacentStrictDescent ends m j k l zero hloop hjk hkl hk0 p hlocal d

/--
[GrahamFiberMinor_of_canonicalMaskAdjacentStrictDescent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitPropagation.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskAdjacentStrictDescent_eq
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
  (hlocal : ∀ p : Finset I × Finset I, CanonicalMaskAdjacentStrictDescent ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskAdjacentStrictDescent ends m j k l zero hloop hjk hkl hk0 hlocal


-- created on 2026-10-23
