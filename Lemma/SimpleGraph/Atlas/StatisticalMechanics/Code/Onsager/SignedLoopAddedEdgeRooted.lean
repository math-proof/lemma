import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAddedEdgeRooted
open Finset SimpleGraph Filter StatMech StatMech.Onsager


/--
[summable_norm_ons_kwAddedEdgeRootedSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAddedEdgeRooted.lean)
-/
@[path]
private lemma summable_norm_ons_kwAddedEdgeRootedSeries_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
  {q : Real}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : Real) * q < 1) :
-- imply
  Summable (fun path : List G.Dart ↦ ‖ons_firstReturnWeight (ons_kwAddedEdgeBaseMatrix G embedding weight) selected selected.symm path‖) := by
-- proof
  apply StatMech.Onsager.summable_norm_ons_kwAddedEdgeRootedSeries embedding weight selected q hq hentry hcard

/--
[ons_kwAddedEdgeRoot_eq_deleted_mul_rooted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAddedEdgeRooted.lean)
-/
@[path]
private lemma ons_kwAddedEdgeRoot_eq_deleted_mul_rooted_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
  {q : Real}
  {t : Complex}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : Real) * q < 1)
  (ht : ‖t‖ ≤ 1) :
-- imply
  ons_kwAddedEdgeRoot G embedding weight selected t = ons_kwAddedEdgeDeletedRoot G embedding weight selected * (1 - t * ons_kwAddedEdgeRootedSeries G embedding weight selected) := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeRoot_eq_deleted_mul_rooted embedding weight selected q hq hentry hsmall hcard t ht

/--
[hasDerivAt_ons_kwAddedEdgeRoot_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAddedEdgeRooted.lean)
-/
@[path]
private lemma hasDerivAt_ons_kwAddedEdgeRoot_zero_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
  {q : Real}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : Real) * q < 1) :
-- imply
  HasDerivAt (ons_kwAddedEdgeRoot G embedding weight selected) (-(ons_kwAddedEdgeDeletedRoot G embedding weight selected * ons_kwAddedEdgeRootedSeries G embedding weight selected)) 0 := by
-- proof
  apply StatMech.Onsager.hasDerivAt_ons_kwAddedEdgeRoot_zero embedding weight selected q hq hentry hsmall hcard


-- created on 2026-10-23
