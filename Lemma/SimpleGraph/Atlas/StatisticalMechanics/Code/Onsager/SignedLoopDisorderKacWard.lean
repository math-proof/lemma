import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[coe_ons_disorderX_eq_kwEvenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDisorderKacWard.lean)
-/
@[path]
private lemma coe_ons_disorderX_eq_kwEvenPolynomial_eq
  [Fintype V]
  [DecidableEq V]
  {Q : Finset (Sym2 V)}
  {x : Real}
-- given
  (hx : x ≠ 0) :
-- imply
  (ons_disorderX G Q x : Complex) = (x : Complex) ^ Q.card * kwEvenPolynomial G (fun e => if e ∈ Q then (x : Complex)⁻¹ else (x : Complex)) := by
-- proof
  apply StatMech.Onsager.coe_ons_disorderX_eq_kwEvenPolynomial hx

/--
[coe_ons_sourceX_eq_kwEvenPolynomial_disorder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDisorderKacWard.lean)
-/
@[path]
private lemma coe_ons_sourceX_eq_kwEvenPolynomial_disorder_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {Q : Finset (Sym2 V)}
  {x : Real}
-- given
  (hQsub : Q ⊆ G.edgeFinset)
  (hQ : StatMech.Sharpness.HasOddBoundary Q {u, v})
  (hx : x ≠ 0) :
-- imply
  (ons_sourceX G {u, v} x : Complex) = (x : Complex) ^ Q.card * kwEvenPolynomial G (fun e => if e ∈ Q then (x : Complex)⁻¹ else (x : Complex)) := by
-- proof
  apply StatMech.Onsager.coe_ons_sourceX_eq_kwEvenPolynomial_disorder hQsub hQ hx

/--
[coe_ons_sourceX_sq_eq_defect_kwDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDisorderKacWard.lean)
-/
@[path]
private lemma coe_ons_sourceX_sq_eq_defect_kwDet_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {u v : V}
  {Q : Finset (Sym2 V)}
  {x : Real}
-- given
  (hQsub : Q ⊆ G.edgeFinset)
  (hQ : StatMech.Sharpness.HasOddBoundary Q {u, v})
  (hx : x ≠ 0) :
-- imply
  (ons_sourceX G {u, v} x : Complex) ^ 2 = (x : Complex) ^ (2 * Q.card) * (1 - kwGraphTransition G (fun e => if e ∈ Q then (x : Complex)⁻¹ else (x : Complex)) embedding.turnPhase).det := by
-- proof
  apply StatMech.Onsager.coe_ons_sourceX_sq_eq_defect_kwDet embedding hQsub hQ hx


-- created on 2026-10-23
