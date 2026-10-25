import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc11bkriffincinc
open Finset StatMech StatMech.Walls


/--
[rc11_deficitIncInc_of_bkr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11bkriffincinc.lean)
-/
@[path]
private lemma rc11_deficitIncInc_of_bkr_eq
-- given
  (h : rc10_BKRSetFamily) :
-- imply
  rc10_DeficitBridgeIncInc := by
-- proof
  apply StatMech.Walls.rc11_deficitIncInc_of_bkr h

/--
[rc11_bkr_of_deficitIncInc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11bkriffincinc.lean)
-/
@[path]
private lemma rc11_bkr_of_deficitIncInc_eq
-- given
  (h : rc10_DeficitBridgeIncInc) :
-- imply
  rc10_BKRSetFamily := by
-- proof
  apply StatMech.Walls.rc11_bkr_of_deficitIncInc h

/--
[rc11_bkr_iff_deficitIncInc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11bkriffincinc.lean)
-/
@[path]
private lemma rc11_bkr_iff_deficitIncInc_eq :
-- imply
  rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc := by
-- proof
  apply StatMech.Walls.rc11_bkr_iff_deficitIncInc

/--
[rc11_deficit_incInc_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11bkriffincinc.lean)
-/
@[path]
private lemma rc11_deficit_incInc_one_eq
  {A B : Set (ConfigSpace (Fin 1))}
  {_ : IsIncreasing A}
  {_ : IsIncreasing B} :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc11_deficit_incInc_one A B _ _


-- created on 2026-10-23
