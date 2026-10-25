import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
open SimpleGraph StatMech StatMech.FK


/--
[bcProb_congr_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreFreeDomination.lean)
-/
@[path]
private lemma bcProb_congr_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G C D : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {p q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (h : C = D) :
-- imply
  bcProb G C p q omega = bcProb G D p q omega := by
-- proof
  apply StatMech.FK.bcProb_congr_boundary G C D h p q omega

/--
[ocd_condFreeProb_innerRestrict_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreFreeDomination.lean)
-/
@[path]
private lemma ocd_condFreeProb_innerRestrict_ge_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {p q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (iota : Vin -> Vout)
  (hiota : Function.Injective iota)
  (hadj : ocd_AdjMatch Gin Gout iota)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph (falseBoundary : Vout -> Prop)) p q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) >= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega := by
-- proof
  apply StatMech.FK.ocd_condFreeProb_innerRestrict_ge Gin Gout iota hiota hadj hp hp1 hq psi hA

/--
[ocd_free_inner_le_outer_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreFreeDomination.lean)
-/
@[path]
private lemma ocd_free_inner_le_outer_fkProb_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (iota : Vin -> Vout)
  (hiota : Function.Injective iota)
  (hadj : ocd_AdjMatch Gin Gout iota)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega) <= ∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * fkProb Gout p q rho := by
-- proof
  apply StatMech.FK.ocd_free_inner_le_outer_fkProb Gin Gout iota hiota hadj hp hp1 hq hA


-- created on 2026-10-23
