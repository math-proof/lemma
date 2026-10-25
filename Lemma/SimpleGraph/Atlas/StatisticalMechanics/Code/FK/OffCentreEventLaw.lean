import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.OffCentreEventLaw
open StatMech StatMech.FK


/--
[ocd_condBcProb_innerEvent_eq_of_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreEventLaw.lean)
-/
@[path]
private lemma ocd_condBcProb_innerEvent_eq_of_pointwise_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {iota : Vin -> Vout}
  {bdryOut : Vout -> Prop}
  [DecidablePred bdryOut]
  {p q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (hiota : Function.Injective iota)
  (hadj : ocd_AdjMatch Gin Gout iota)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (mu : ConfigSpace (Sym2 Vin) -> Real)
  (hmu : ∀ omega, condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset iota) psi (ocd_psiExt iota psi omega) = mu omega) :
-- imply
  (∑ rho : ConfigSpace (Sym2 Vout), (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset iota) psi rho) = ∑ omega : ConfigSpace (Sym2 Vin), A.indicator (fun _ => (1 : Real)) omega * mu omega := by
-- proof
  apply StatMech.FK.ocd_condBcProb_innerEvent_eq_of_pointwise hiota hadj hp hp1 hq psi mu hmu A


-- created on 2026-10-23
