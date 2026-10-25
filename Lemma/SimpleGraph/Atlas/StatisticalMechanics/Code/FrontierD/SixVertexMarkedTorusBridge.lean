import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[eval_sixVertexLocalMarkedPatternWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma eval_sixVertexLocalMarkedPatternWeight_eq
  {t : Real}
  {p : SixVertexLocalIncomingPattern} :
-- imply
  eval t (sixVertexLocalMarkedPatternWeight p) = sixVertexLocalPatternWeight (2 + t) p := by
-- proof
  apply StatMech.FrontierD.eval_sixVertexLocalMarkedPatternWeight t p

/--
[sixVertexTorusMarkedWeight_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma sixVertexTorusMarkedWeight_eq_pow_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
-- given
  (homega : omega.IceRule) :
-- imply
  sixVertexTorusMarkedWeight omega = (C 2 + X) ^ sixVertexTorusCTypeCount omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusMarkedWeight_eq_pow omega homega

/--
[sixVertexTorusMarkedWeight_eq_zero_of_not_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma sixVertexTorusMarkedWeight_eq_zero_of_not_ice_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
-- given
  (homega : ¬ omega.IceRule) :
-- imply
  sixVertexTorusMarkedWeight omega = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusMarkedWeight_eq_zero_of_not_ice omega homega

/--
[coeff_sixVertexTorusMarkedWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma coeff_sixVertexTorusMarkedWeight_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {k : Nat} :
-- imply
  (sixVertexTorusMarkedWeight omega).coeff k = if omega.IceRule then (2 : Real) ^ (sixVertexTorusCTypeCount omega - k) * (sixVertexTorusCTypeCount omega).choose k else 0 := by
-- proof
  apply StatMech.FrontierD.coeff_sixVertexTorusMarkedWeight omega k

/--
[eval_sixVertexTorusMarkedWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma eval_sixVertexTorusMarkedWeight_eq
  {T : EvenTorus}
  {t : Real}
  {omega : SixVertexArrows T} :
-- imply
  eval t (sixVertexTorusMarkedWeight omega) = omega.weight (2 + t) := by
-- proof
  apply StatMech.FrontierD.eval_sixVertexTorusMarkedWeight t omega

/--
[eval_sixVertexTorusMarkedSectorPartitionPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma eval_sixVertexTorusMarkedSectorPartitionPolynomial_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)}
  {t : Real} :
-- imply
  eval t (sixVertexTorusMarkedSectorPartitionPolynomial T n) = svTorusSectorArrowPartitionSum T n (2 + t) := by
-- proof
  apply StatMech.FrontierD.eval_sixVertexTorusMarkedSectorPartitionPolynomial T n t

/--
[sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)} :
-- imply
  sixVertexTorusMarkedSectorPartitionPolynomial T n = sixVertexShiftedSectorTracePolynomial T.width T.height n.val := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace T n

/--
[sixVertexMarkedSectorTraceCoefficient_eq_torus_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma sixVertexMarkedSectorTraceCoefficient_eq_torus_sum_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)}
  {k : Nat} :
-- imply
  sixVertexMarkedSectorTraceCoefficient T.width T.height n.val k = ∑ omega : SixVertexArrows T, if sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then (sixVertexTorusMarkedWeight omega).coeff k else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorTraceCoefficient_eq_torus_sum T n k

/--
[sixVertexMarkedSectorTraceCoefficient_eq_colored_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean)
-/
@[path]
private lemma sixVertexMarkedSectorTraceCoefficient_eq_colored_count_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)}
  {k : Nat} :
-- imply
  sixVertexMarkedSectorTraceCoefficient T.width T.height n.val k = ∑ omega : SixVertexArrows T, if sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then if omega.IceRule then (2 : Real) ^ (sixVertexTorusCTypeCount omega - k) * (sixVertexTorusCTypeCount omega).choose k else 0 else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorTraceCoefficient_eq_colored_count T n k


-- created on 2026-10-23
