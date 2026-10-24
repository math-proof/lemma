import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBarrierConnectionProduct
open StatMech StatMech.FrontierD


/--
[fkRectRightBand_barrierConnectionProduct_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierConnectionProduct.lean)
-/
@[path]
private lemma fkRectRightBand_barrierConnectionProduct_le_eq
  {R : FKRectTorus}
  {leftRight cut lower upper : Nat}
  {q : Real}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration}
  {t : Finset (FKRectRightStripBandVertex R cut lower upper × FKRectRightStripBandVertex R cut lower upper)}
-- given
  (hsep : leftRight < cut)
  (hlower : 1 ≤ lower)
  (hq : 1 ≤ q)
  (hI : ∀ a ∈ I, fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a)) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectLeftBarrierWithSeamPattern R leftRight I eta) ≤ ∑ rho, (fkRectRightBandBarrierConnectionEvent R leftRight cut lower upper I eta t).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectRightBand_barrierConnectionProduct_le R leftRight cut lower upper hsep hlower hq I hI eta t


-- created on 2026-10-23
