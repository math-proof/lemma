/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part4
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def generalFreeBoxCurrentMeasure {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let G := interactionBoxGraph d n
  let Jn := interactionBoxCoupling J n
  let hJn : forall e, 0 <= Jn e := fun e =>
    hJ (Sym2.map Subtype.val e)
  ⟨((sourcelessCurrentPMF G beta Jn hbeta hJn).toMeasure).map
      (extendInteractionBoxCurrent d n),
    inferInstance⟩


noncomputable def interactionPlusInterior (d n : Nat) :
    Finset (interactionBoxVertices d (2 * n + 1)) := by
  classical
  exact Finset.univ.filter fun x => x.1 ∈ box d n


noncomputable def generalPlusBoxCurrentMeasure {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let r := 2 * n + 1
  let G := interactionBoxGraph d r
  let Jn := interactionBoxCoupling J r
  let hJn : forall e, 0 <= Jn e := fun e =>
    hJ (Sym2.map Subtype.val e)
  ⟨((boundaryCurrentPMF G beta Jn hbeta hJn
      (interactionPlusInterior d n)).toMeasure).map
      (extendInteractionBoxCurrent d r),
    inferInstance⟩

end StatMech.FrontierB
