import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEvenSymmetricLift_castAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_castAdd_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexEvenSymmetricLift m q (Fin.castAdd m j) = -q j.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_castAdd m q j

/--
[sixVertexEvenSymmetricLift_natAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_natAdd_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexEvenSymmetricLift m q (Fin.natAdd m j) = q j := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_natAdd m q j

/--
[sixVertexEvenSymmetricLift_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_symmetric_eq
  {m : Nat}
  {q : Fin m → Real} :
-- imply
  SixVertexRootSymmetric (sixVertexEvenSymmetricLift m q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_symmetric m q

/--
[sixVertexEvenSymmetricLift_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_injective_eq
  {m : Nat} :
-- imply
  Function.Injective (sixVertexEvenSymmetricLift m) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_injective m

/--
[analyticAt_sixVertexEvenSymmetricBetheResidual_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexEvenSymmetricBetheResidual_family_eq
  {N m : Nat}
  {q : Real × (Fin m → Real)}
-- given
  (hc : 2 < q.1) :
-- imply
  AnalyticAt Real (fun z : Real × (Fin m → Real) => sixVertexEvenSymmetricBetheResidual N m z.1 z.2) q := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexEvenSymmetricBetheResidual_family N m q hc

/--
[analyticAt_sixVertexEvenSymmetricBetheResidualGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexEvenSymmetricBetheResidualGraph_eq
  {N m : Nat}
  {q : Real × (Fin m → Real)}
-- given
  (hc : 2 < q.1) :
-- imply
  AnalyticAt Real (sixVertexEvenSymmetricBetheResidualGraph N m) q := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexEvenSymmetricBetheResidualGraph N m q hc

/--
[sixVertexBetheResidual_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheResidual_symmetric_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  SixVertexRootSymmetric (fun j => sixVertexBetheResidual c N n p j) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheResidual_symmetric hp

/--
[sixVertexEvenSymmetricBetheResidual_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheResidual_eq_zero_iff_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real} :
-- imply
  sixVertexEvenSymmetricBetheResidual N m c q = 0 ↔ SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheResidual_eq_zero_iff N m c q

/--
[sixVertexEvenSymmetricBetheResidualGraph_fderiv_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheResidualGraph_fderiv_injective_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hjac : Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q)) :
-- imply
  Function.Injective (fderiv Real (sixVertexEvenSymmetricBetheResidualGraph N m) (c, q)) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheResidualGraph_fderiv_injective hc hjac

/--
[exists_sixVertexLocalAnalyticEvenSymmetricBetheBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexLocalAnalyticEvenSymmetricBetheBranch_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q))
  (hjac : Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q)) :
-- imply
  Nonempty (SixVertexLocalAnalyticEvenSymmetricBetheBranch N m c q) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalAnalyticEvenSymmetricBetheBranch hc hsol hjac


-- created on 2026-10-23
