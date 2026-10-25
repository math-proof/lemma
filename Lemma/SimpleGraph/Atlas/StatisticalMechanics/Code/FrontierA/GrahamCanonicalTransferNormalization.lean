import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferNormalization.Part2
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[exchangeFirstRow_no_incident_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferNormalization.lean)
-/
@[path]
private lemma exchangeFirstRow_no_incident_zero_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {K L : Finset I}
  {k zero : W}
-- given
  (hL : ¬ connK ends L k zero) :
-- imply
  ∀ i ∈ exchangeFirstRow ends K L k zero, zero ∉ ends i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exchangeFirstRow_no_incident_zero hL

/--
[exchangeSecondRow_no_incident_k](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferNormalization.lean)
-/
@[path]
private lemma exchangeSecondRow_no_incident_k_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {K L : Finset I}
  {k zero : W}
-- given
  (hK : ¬ connK ends K k zero) :
-- imply
  ∀ i ∈ exchangeSecondRow ends K L k zero, k ∉ ends i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exchangeSecondRow_no_incident_k hK

/--
[edgeComponent_eq_empty_of_no_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferNormalization.lean)
-/
@[path]
private lemma edgeComponent_eq_empty_of_no_incident_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {root : W}
-- given
  (ends : I -> Sym2 W)
  (hinc : ∀ i ∈ K, root ∉ ends i) :
-- imply
  edgeComponent ends K root = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.edgeComponent_eq_empty_of_no_incident ends K root hinc

/--
[canonicalTransferUnion_selfSwap_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferNormalization.lean)
-/
@[path]
private lemma canonicalTransferUnion_selfSwap_eq_empty_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  canonicalTransferUnion ends m k zero (balancedSwap m (canonicalMiddleTransfer ends m c k zero) (canonicalOuterTransfer ends m c k zero) c) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferUnion_selfSwap_eq_empty hloop hjk hkl hc

/--
[canonicalTransferSymmDiff_eq_rowSymmDiff_of_normalRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferNormalization.lean)
-/
@[path]
private lemma canonicalTransferSymmDiff_eq_rowSymmDiff_of_normalRows_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c d : ↑m -> Fin 4)
  (hac : canonicalNormalRow ends m k zero a = canonicalNormalRow ends m k zero c)
  (hbd : canonicalNormalRow ends m k zero b = canonicalNormalRow ends m k zero d)
  (hrow : rowClass m c 0 ∆ rowClass m d 0 = canonicalTransferUnion ends m k zero a ∆ canonicalTransferUnion ends m k zero b) :
-- imply
  canonicalTransferUnion ends m k zero c ∆ canonicalTransferUnion ends m k zero d = rowClass m a 0 ∆ rowClass m b 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferSymmDiff_eq_rowSymmDiff_of_normalRows ends m k zero a b c d hac hbd hrow


-- created on 2026-10-23
