import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FreeNestedDecreasing
open Finset Set SimpleGraph StatMech StatMech.FK


/--
[bdp_free_outer_dominated_inner_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeNestedDecreasing.lean)
-/
@[path]
private lemma bdp_free_outer_dominated_inner_decreasing_eq
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {iota : Vin → Vout}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsDecreasing A) :
-- imply
  (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * fkProb Gout p q rho) ≤ ∑ omega, A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega := by
-- proof
  apply StatMech.FK.bdp_free_outer_dominated_inner_decreasing hiota hadjm hp hp1 hq hA


-- created on 2026-10-23
