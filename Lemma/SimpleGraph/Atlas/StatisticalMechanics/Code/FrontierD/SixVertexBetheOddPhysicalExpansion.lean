import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddPhysicalExpansion
open Finset StatMech StatMech.FrontierD


/--
[sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddPhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero_eq
  {p : Real}
-- given
  (hp : p ∈ Set.Ioo (-Real.pi) Real.pi)
  (hne : p ≠ 0) :
-- imply
  sixVertexBethePhase p ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero hp hne

/--
[sixVertexFixedChargeBetheRoots_phase_ne_one_of_odd_charge_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddPhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_phase_ne_one_of_odd_charge_of_ne_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c)
  (hr : Odd r)
  (hj : j ≠ sixVertexFixedChargeBetheCentralIndex r k) :
-- imply
  sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j) ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_phase_ne_one_of_odd_charge_of_ne hc hr k hj


-- created on 2026-10-23
