/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part10
import Abbrev.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor
open MeasureTheory Set


namespace StatMech.FK

theorem pottsJoint_fst_equivariant {d q : Nat}
    (g : Multiplicative (Lattice.Site d))
    (joint : (Lattice.Site d -> Fin q) ×
      ConfigSpace (Sym2 (Lattice.Site d))) :
    (pottsJointShift g joint).1 = pottsSpinShift g joint.1 := rfl


theorem pottsClusterSumJointMeasure_isErgodicFor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    (hsource : IsErgodicFor pottsClusterFactorInputShift
      (edgeMeasure.prod (pottsIIDLabelMeasure d q))) :
    IsErgodicFor pottsJointShift
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure) := by
  exact hsource.map (pottsClusterSumJointFactor boundaryColor)
    (measurable_pottsClusterSumJointFactor boundaryColor)
    (fun g =>
      ((measurable_pi_lambda _ fun x =>
        measurable_pi_apply (g⁻¹ • x)).comp measurable_fst).prodMk
        ((ConfigSpace.measurable_shift g).comp measurable_snd))
    (pottsClusterSumJointFactor_shift boundaryColor)


theorem pottsClusterSumSpinMarginal_isErgodicFor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    (hjoint : IsErgodicFor pottsJointShift
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure)) :
    IsErgodicFor pottsSpinShift
      (Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure)) := by
  exact hjoint.map Prod.fst measurable_fst
    (fun _ => measurable_pi_lambda _ fun x => measurable_pi_apply _)
    (fun _ _ => rfl)

end StatMech.FK
