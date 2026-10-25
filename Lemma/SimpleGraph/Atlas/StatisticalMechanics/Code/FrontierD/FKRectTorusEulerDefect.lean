import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
open StatMech StatMech.FrontierD


/--
[fkRectCriticalReducedWeight_eq_sqrt_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_eq_sqrt_pow_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalReducedWeight R q omega = Real.sqrt q ^ (fkRectOpenEdgeCount R omega + 2 * fkRectNumClusters R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_eq_sqrt_pow R hq omega

/--
[fkRectCriticalReducedWeight_eq_loop_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_eq_loop_defect_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalReducedWeight R q omega = Real.sqrt q ^ (R.width * R.height : Nat) * Real.sqrt q ^ fkRectMedialLoopCount R omega * Real.sqrt q ^ fkRectEulerHomologyDefect R omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_eq_loop_defect R hq omega

/--
[fkRectRandomClusterWeight_critical_eq_loop_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean)
-/
@[path]
private lemma fkRectRandomClusterWeight_critical_eq_loop_defect_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectRandomClusterWeight R (fkRectCriticalP q) q omega = fkRectCriticalLoopNormalization R q * Real.sqrt q ^ fkRectMedialLoopCount R omega * Real.sqrt q ^ fkRectEulerHomologyDefect R omega := by
-- proof
  apply StatMech.FrontierD.fkRectRandomClusterWeight_critical_eq_loop_defect R hq omega

/--
[fkRectRandomClusterWeight_critical_eq_loop_net](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean)
-/
@[path]
private lemma fkRectRandomClusterWeight_critical_eq_loop_net_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
  {s : Nat}
-- given
  (hq : 0 < q)
  (hnet : fkRectEulerHomologyDefect R omega = 2 * (s : Int)) :
-- imply
  fkRectRandomClusterWeight R (fkRectCriticalP q) q omega = fkRectCriticalLoopNormalization R q * Real.sqrt q ^ fkRectMedialLoopCount R omega * q ^ s := by
-- proof
  apply StatMech.FrontierD.fkRectRandomClusterWeight_critical_eq_loop_net R hq omega s hnet


-- created on 2026-10-23
