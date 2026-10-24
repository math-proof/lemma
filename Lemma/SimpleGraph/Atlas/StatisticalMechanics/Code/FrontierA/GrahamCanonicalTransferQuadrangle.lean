import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferQuadrangle
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalTransfer_quadrangleCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalTransfer_quadrangleCompletion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c : ↑m -> Fin 4) :
-- imply
  balancedSwap m (canonicalMiddleTransfer ends m b k zero) (canonicalOuterTransfer ends m b k zero) (canonicalQuadrangleCompletion ends m k zero a b c) = balancedSwap m (canonicalMiddleTransfer ends m a k zero) (canonicalOuterTransfer ends m a k zero) c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransfer_quadrangleCompletion ends m k zero a b c

/--
[canonicalQuadrangleCompletion_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_involutive_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c : ↑m -> Fin 4) :
-- imply
  canonicalQuadrangleCompletion ends m k zero a b (canonicalQuadrangleCompletion ends m k zero a b c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_involutive ends m k zero a b c

/--
[canonicalQuadrangleCompletion_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_comm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c : ↑m -> Fin 4) :
-- imply
  canonicalQuadrangleCompletion ends m k zero a b c = canonicalQuadrangleCompletion ends m k zero b a c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_comm ends m k zero a b c

/--
[canonicalQuadrangleCompletion_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_trans_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c d : ↑m -> Fin 4) :
-- imply
  canonicalQuadrangleCompletion ends m k zero b c (canonicalQuadrangleCompletion ends m k zero a b d) = canonicalQuadrangleCompletion ends m k zero a c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_trans ends m k zero a b c d

/--
[canonicalQuadrangleCompletion_changes_commute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_changes_commute_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b r s x : ↑m -> Fin 4) :
-- imply
  canonicalQuadrangleCompletion ends m k zero a b (canonicalQuadrangleCompletion ends m k zero r s x) = canonicalQuadrangleCompletion ends m k zero r s (canonicalQuadrangleCompletion ends m k zero a b x) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_changes_commute ends m k zero a b r s x

/--
[canonicalTransferWorks_quadrangleCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalTransferWorks_quadrangleCompletion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c : ↑m -> Fin 4)
  (hac : CanonicalTransferWorks ends m k zero a c) :
-- imply
  CanonicalTransferWorks ends m k zero b (canonicalQuadrangleCompletion ends m k zero a b c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_quadrangleCompletion ends m k zero a b c hac

/--
[canonicalTransferWorks_quadrangleCompletion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalTransferWorks_quadrangleCompletion_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c : ↑m -> Fin 4) :
-- imply
  CanonicalTransferWorks ends m k zero a (canonicalQuadrangleCompletion ends m k zero a b c) ↔ CanonicalTransferWorks ends m k zero b c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_quadrangleCompletion_iff ends m k zero a b c

/--
[canonicalTransferWorks_new_quadrangleCompletion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalTransferWorks_new_quadrangleCompletion_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c : ↑m -> Fin 4) :
-- imply
  CanonicalTransferWorks ends m k zero b (canonicalQuadrangleCompletion ends m k zero a b c) ↔ CanonicalTransferWorks ends m k zero a c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_new_quadrangleCompletion_iff ends m k zero a b c

/--
[leftPattern_of_sourceless_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma leftPattern_of_sourceless_balancedSwap_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m X Y : Finset I}
  {A B : Finset W}
  {u v : W}
  {c : ↑m -> Fin 4}
-- given
  (hleft : LeftPattern ends m A B u v c)
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
  (hsrcX : sources ends X = ∅)
  (hsrcY : sources ends Y = ∅)
  (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
-- imply
  LeftPattern ends m A B u v (balancedSwap m X Y c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_of_sourceless_balancedSwap hleft hX hY hsrcX hsrcY hdisc

/--
[canonicalMaskTransferAdjacent_quadrangleCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalMaskTransferAdjacent_quadrangleCompletion_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hac : CanonicalTransferWorks ends m k zero a.1.1 c.1.1)
  (hdisc : RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero) :
-- imply
  CanonicalMaskTransferAdjacent ends m j k l zero p c (canonicalQuadrangleCompletionMemOfDisconnects ends m j k l zero hloop hjk hkl p a b c hdisc) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferAdjacent_quadrangleCompletion hloop hjk hkl a b c hac hdisc

/--
[canonicalQuadrangleCompletion_rowCard_eq_transferCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_rowCard_eq_transferCard_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hdisc : RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero) :
-- imply
  let d := canonicalQuadrangleCompletionMemOfDisconnects ends m j k l zero hloop hjk hkl p a b c hdisc; #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) = #(canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_rowCard_eq_transferCard hloop hjk hkl a b c hdisc

/--
[canonicalQuadrangleCompletion_score_lt_of_rowCard_lt_transferCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_score_lt_of_rowCard_lt_transferCard_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hdisc : RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero)
  (hlt : #(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) < #(canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1)) :
-- imply
  let d := canonicalQuadrangleCompletionMemOfDisconnects ends m j k l zero hloop hjk hkl p a b c hdisc; canonicalCoveragePairScore ends m k zero a.1.1 b.1.1 < canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_score_lt_of_rowCard_lt_transferCard hloop hjk hkl a b c hdisc hlt


-- created on 2026-10-23
