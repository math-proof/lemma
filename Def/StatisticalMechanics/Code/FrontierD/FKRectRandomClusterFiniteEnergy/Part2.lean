/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

noncomputable def fkRectGraphClosedFibre
    (R : FKRectTorus)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    Finset (FKRectGraphConfiguration R) :=
  Finset.univ.filter fun eta =>
    eta e = false ∧ ∀ e' ∈ I, eta e' = false

end
end StatMech.FrontierD
