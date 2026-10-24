import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianAtlas
open SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.CriticalIsoradialGenusZeroOneEmbedding


/--
[det_eq_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianAtlas.lean)
-/
@[path]
private lemma det_eq_laplacian_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {DualVertex Q Qstar Component : Type u}
  [Fintype DualVertex]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  [Fintype Component]
  [DecidableEq Component]
  {embedding : CriticalIsoradialGenusZeroOneEmbedding g G DualVertex Q Qstar Component} :
-- imply
  (1 - embedding.isoradial.primalKacWard).det = (-1 : Complex) ^ coneExceptionCount embedding.isoradial.primalExceptional * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card (finiteGraphEdge G)) * kwLaplacianEdgePrefactor embedding.isoradial.theta * (finiteTwistedLaplacian (isoradialLaplacianConductance embedding.thetaVertex) embedding.transport).det := by
-- proof
  apply StatMech.FrontierA.CriticalIsoradialGenusZeroOneEmbedding.det_eq_laplacian embedding


-- created on 2026-10-23
