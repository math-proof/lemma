import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopSourceRootedDerivative
open Filter SimpleGraph StatMech StatMech.Onsager


/--
[derivative_eq_source_of_eventually_sq_eq_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma derivative_eq_source_of_eventually_sq_eq_sq_eq
  {base source rootDeriv : Complex}
-- given
  (root : Complex -> Complex)
  (hroot : HasDerivAt root rootDeriv 0)
  (hzero : root 0 = base)
  (hbase : base ≠ 0)
  (hsq : (fun t => root t ^ 2) =ᶠ[nhds 0] (fun t => (base + t * source) ^ 2)) :
-- imply
  rootDeriv = source := by
-- proof
  apply StatMech.Onsager.derivative_eq_source_of_eventually_sq_eq_sq root base source rootDeriv hroot hzero hbase hsq

/--
[kwEvenPolynomial_scaleGraphEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma kwEvenPolynomial_scaleGraphEdge_affine_eq
  [Fintype V]
  [DecidableEq V]
  {selected : G.Dart}
  {t : Complex}
-- given
  (weight : Sym2 V -> Complex) :
-- imply
  kwEvenPolynomial G (kwScaleGraphEdgeWeight weight selected.edge t) = ons_kwAddedEdgeEvenBase G weight selected + t * ons_kwAddedEdgeEvenSource G weight selected := by
-- proof
  apply StatMech.Onsager.kwEvenPolynomial_scaleGraphEdge_affine weight selected t

/--
[ons_kwAddedEdgeRoot_sq_eq_evenPolynomial_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma ons_kwAddedEdgeRoot_sq_eq_evenPolynomial_sq_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {selected : G.Dart}
  {q : Real}
  {t : Complex}
-- given
  (weight : Sym2 V -> Complex)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : Real) * q < 1)
  (ht : ‖t‖ ≤ 1) :
-- imply
  ons_kwAddedEdgeRoot G embedding weight selected t ^ 2 = kwEvenPolynomial G (kwScaleGraphEdgeWeight weight selected.edge t) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeRoot_sq_eq_evenPolynomial_sq embedding weight selected q hq hentry hcard t ht

/--
[ons_kwAddedEdgeRoot_zero_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma ons_kwAddedEdgeRoot_zero_ne_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {selected : G.Dart}
-- given
  (weight : Sym2 V -> Complex) :
-- imply
  ons_kwAddedEdgeRoot G embedding weight selected 0 ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeRoot_zero_ne embedding weight selected

/--
[ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {selected : G.Dart}
  {q : Real}
  {t : Complex}
-- given
  (weight : Sym2 V -> Complex)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : Real) * q < 1)
  (ht : ‖t‖ ≤ 1) :
-- imply
  ons_kwAddedEdgeRoot G embedding weight selected t ^ 2 = (ons_kwAddedEdgeRoot G embedding weight selected 0 + t * ons_kwAddedEdgeNormalizedSource G embedding weight selected) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq embedding weight selected q hq hentry hcard t ht

/--
[eventually_ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma eventually_ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {selected : G.Dart}
  {q : Real}
-- given
  (weight : Sym2 V -> Complex)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : Real) * q < 1) :
-- imply
  (fun t => ons_kwAddedEdgeRoot G embedding weight selected t ^ 2) =ᶠ[nhds 0] (fun t => (ons_kwAddedEdgeRoot G embedding weight selected 0 + t * ons_kwAddedEdgeNormalizedSource G embedding weight selected) ^ 2) := by
-- proof
  apply StatMech.Onsager.eventually_ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq embedding weight selected q hq hentry hcard

/--
[ons_source_eq_neg_deleted_mul_rooted_of_local_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma ons_source_eq_neg_deleted_mul_rooted_of_local_square_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {selected : G.Dart}
  {q : Real}
  {base source : Complex}
-- given
  (weight : Sym2 V -> Complex)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : Real) * q < 1)
  (hzero : ons_kwAddedEdgeRoot G embedding weight selected 0 = base)
  (hbase : base ≠ 0)
  (hsq : (fun t => ons_kwAddedEdgeRoot G embedding weight selected t ^ 2) =ᶠ[nhds 0] (fun t => (base + t * source) ^ 2)) :
-- imply
  source = -(ons_kwAddedEdgeDeletedRoot G embedding weight selected * ons_kwAddedEdgeRootedSeries G embedding weight selected) := by
-- proof
  apply StatMech.Onsager.ons_source_eq_neg_deleted_mul_rooted_of_local_square embedding weight selected q hq hentry hsmall hcard base source hzero hbase hsq

/--
[ons_kwAddedEdgeNormalizedSource_eq_neg_deleted_mul_rooted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean)
-/
@[path]
private lemma ons_kwAddedEdgeNormalizedSource_eq_neg_deleted_mul_rooted_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {selected : G.Dart}
  {q : Real}
-- given
  (weight : Sym2 V -> Complex)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : Real) * q < 1) :
-- imply
  ons_kwAddedEdgeNormalizedSource G embedding weight selected = -(ons_kwAddedEdgeDeletedRoot G embedding weight selected * ons_kwAddedEdgeRootedSeries G embedding weight selected) := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeNormalizedSource_eq_neg_deleted_mul_rooted embedding weight selected q hq hentry hsmall hcard


-- created on 2026-10-23
