import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic.Part4
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexOddSymmetricLift_negative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_negative_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexOddSymmetricLift m q (sixVertexOddNegativeIndex m j) = -q j.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_negative m q j

/--
[sixVertexOddSymmetricLift_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_central_eq
  {m : Nat}
  {q : Fin m → Real} :
-- imply
  sixVertexOddSymmetricLift m q (sixVertexOddCentralIndex m) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_central m q

/--
[sixVertexOddSymmetricLift_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_positive_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexOddSymmetricLift m q (sixVertexOddPositiveIndex m j) = q j := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_positive m q j

/--
[sixVertexOddNegativeIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddNegativeIndex_rev_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  (sixVertexOddNegativeIndex m j).rev = sixVertexOddPositiveIndex m j.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexOddNegativeIndex_rev m j

/--
[sixVertexOddCentralIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddCentralIndex_rev_eq
  {m : Nat} :
-- imply
  (sixVertexOddCentralIndex m).rev = sixVertexOddCentralIndex m := by
-- proof
  apply StatMech.FrontierD.sixVertexOddCentralIndex_rev m

/--
[sixVertexOddPositiveIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddPositiveIndex_rev_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  (sixVertexOddPositiveIndex m j).rev = sixVertexOddNegativeIndex m j.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexOddPositiveIndex_rev m j

/--
[sixVertexOddSymmetricLift_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_symmetric_eq
  {m : Nat}
  {q : Fin m → Real} :
-- imply
  SixVertexRootSymmetric (sixVertexOddSymmetricLift m q) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_symmetric m q

/--
[sixVertexOddSymmetricLift_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_injective_eq
  {m : Nat} :
-- imply
  Function.Injective (sixVertexOddSymmetricLift m) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_injective m

/--
[analyticAt_sixVertexOddSymmetricBetheResidual_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexOddSymmetricBetheResidual_family_eq
  {N m : Nat}
  {q : Real × (Fin m → Real)}
-- given
  (hc : 2 < q.1) :
-- imply
  AnalyticAt Real (fun z : Real × (Fin m → Real) => sixVertexOddSymmetricBetheResidual N m z.1 z.2) q := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexOddSymmetricBetheResidual_family N m q hc

/--
[analyticAt_sixVertexOddSymmetricBetheResidualGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexOddSymmetricBetheResidualGraph_eq
  {N m : Nat}
  {q : Real × (Fin m → Real)}
-- given
  (hc : 2 < q.1) :
-- imply
  AnalyticAt Real (sixVertexOddSymmetricBetheResidualGraph N m) q := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexOddSymmetricBetheResidualGraph N m q hc

/--
[sixVertexOddSymmetricBetheResidual_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheResidual_eq_zero_iff_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real} :
-- imply
  sixVertexOddSymmetricBetheResidual N m c q = 0 ↔ SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheResidual_eq_zero_iff N m c q

/--
[sixVertexOddSymmetricBetheResidualGraph_fderiv_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheResidualGraph_fderiv_injective_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hjac : Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q)) :
-- imply
  Function.Injective (fderiv Real (sixVertexOddSymmetricBetheResidualGraph N m) (c, q)) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheResidualGraph_fderiv_injective hc hjac

/--
[exists_sixVertexLocalAnalyticOddSymmetricBetheBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexLocalAnalyticOddSymmetricBetheBranch_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q))
  (hjac : Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q)) :
-- imply
  Nonempty (SixVertexLocalAnalyticOddSymmetricBetheBranch N m c q) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalAnalyticOddSymmetricBetheBranch hc hsol hjac


-- created on 2026-10-23
