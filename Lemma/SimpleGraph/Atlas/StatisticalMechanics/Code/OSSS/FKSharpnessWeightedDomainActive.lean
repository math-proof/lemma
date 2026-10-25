import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
open Finset Set SimpleGraph StatMech StatMech.FK


/--
[ocd_innerRestrictActive_restrictActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomainActive.lean)
-/
@[path]
private lemma ocd_innerRestrictActive_restrictActive_eq
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {rho : ConfigSpace (Sym2 Vout)}
-- given
  (iota : Vin -> Vout)
  (hadjm : ocd_AdjMatch Gin Gout iota) :
-- imply
  ocd_innerRestrictActive Gin Gout iota hadjm (restrictActive Gout rho) = restrictActive Gin (ocd_innerRestrict iota rho) := by
-- proof
  apply StatMech.FK.ocd_innerRestrictActive_restrictActive Gin Gout iota hadjm rho

/--
[ocd_free_inner_dominated_activeBCMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomainActive.lean)
-/
@[path]
private lemma ocd_free_inner_dominated_activeBCMean_eq
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {A : Set (ConfigSpace Gin.edgeSet)}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfIn : forall e, 0 < pfIn e)
  (hpfIn1 : forall e, pfIn e < 1)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean Gin ⊥ pfIn q (A.indicator fun _ => (1 : Real)) <= activeBCMean Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) pfOut q (fun rho => A.indicator (fun _ => (1 : Real)) (ocd_innerRestrictActive Gin Gout iota hadjm rho)) := by
-- proof
  apply StatMech.FK.ocd_free_inner_dominated_activeBCMean Gin Gout iota bdryOut hiota hadjm hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hA

/--
[ocd_wired_inner_dominated_activeBCMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomainActive.lean)
-/
@[path]
private lemma ocd_wired_inner_dominated_activeBCMean_eq
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {A : Set (ConfigSpace Gin.edgeSet)}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (bdryIn : Vin -> Prop)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfIn : forall e, 0 < pfIn e)
  (hpfIn1 : forall e, pfIn e < 1)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 1 <= q)
  (hwire : forall psi : ConfigSpace (Sym2 Vout), ocd_inducedWiring Gout iota bdryOut psi <= StatMech.Lattice.boundaryCliqueGraph bdryIn)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) pfOut q (fun rho => A.indicator (fun _ => (1 : Real)) (ocd_innerRestrictActive Gin Gout iota hadjm rho)) <= activeBCMean Gin (StatMech.Lattice.boundaryCliqueGraph bdryIn) pfIn q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.ocd_wired_inner_dominated_activeBCMean Gin Gout iota bdryOut hiota hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hwire hA


-- created on 2026-10-23
