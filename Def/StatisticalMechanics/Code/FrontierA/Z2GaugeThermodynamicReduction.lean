/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCriticalCoupling
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThermodynamicReduction
open Filter Set Topology


namespace StatMech.FrontierA

noncomputable def cubicalSquareWilsonExpectation
    (beta : Real) (n : Nat) : Real :=
  gaugeWilsonExpectation
    (cubicalPlaquetteIncidence (a := n + 1) (b := n + 1) (c := n + 1))
    (fun _ : CubicalPlaquette (n + 1) (n + 1) (n + 1) => beta)
    (cubicalXYLoop (a := n + 1) (b := n + 1) (c := n + 1)
      (0 : Fin (n + 1 + 1)))

end StatMech.FrontierA
