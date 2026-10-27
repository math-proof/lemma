import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor.Part2
open MeasureTheory Set StatMech StatMech.FK


/--
[IsErgodicFor.map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean)
-/
@[path]
private lemma map_eq
  [MeasurableSpace Omega]
  [MeasurableSpace Xi]
  {sourceShift : G -> Omega -> Omega}
  {targetShift : G -> Xi -> Xi}
  {mu : Measure Omega}
-- given
  (hergodic : IsErgodicFor sourceShift mu)
  (factor : Omega -> Xi)
  (hfactor : Measurable factor)
  (htarget : ∀ g, Measurable (targetShift g))
  (hequivariant : ∀ g omega, factor (sourceShift g omega) = targetShift g (factor omega)) :
-- imply
  IsErgodicFor targetShift (Measure.map factor mu) := by
-- proof
  apply StatMech.FK.IsErgodicFor.map hergodic factor hfactor htarget hequivariant

/--
[pottsJoint_fst_equivariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean)
-/
@[path]
private lemma pottsJoint_fst_equivariant_eq
  {d q : Nat}
  {g : Multiplicative (Lattice.Site d)}
-- given
  (joint : (Lattice.Site d -> Fin q) × ConfigSpace (Sym2 (Lattice.Site d))) :
-- imply
  (pottsJointShift g joint).1 = pottsSpinShift g joint.1 := by
-- proof
  apply StatMech.FK.pottsJoint_fst_equivariant g joint

/--
[pottsClusterSumJointMeasure_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Lattice.Site d)))}
-- given
  (hsource : IsErgodicFor pottsClusterFactorInputShift (edgeMeasure.prod (pottsIIDLabelMeasure d q))) :
-- imply
  IsErgodicFor pottsJointShift (pottsClusterSumJointMeasure boundaryColor edgeMeasure) := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_isErgodicFor boundaryColor edgeMeasure hsource

/--
[pottsClusterSumSpinMarginal_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean)
-/
@[path]
private lemma pottsClusterSumSpinMarginal_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Lattice.Site d)))}
-- given
  (hjoint : IsErgodicFor pottsJointShift (pottsClusterSumJointMeasure boundaryColor edgeMeasure)) :
-- imply
  IsErgodicFor pottsSpinShift (Measure.map Prod.fst (pottsClusterSumJointMeasure boundaryColor edgeMeasure)) := by
-- proof
  apply StatMech.FK.pottsClusterSumSpinMarginal_isErgodicFor boundaryColor edgeMeasure hjoint


-- created on 2026-10-23
