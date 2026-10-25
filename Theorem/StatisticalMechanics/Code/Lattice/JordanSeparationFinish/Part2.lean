/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanSeparationFinish
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jsf_dualEulerCount_iff (P : PlanarZ2Subgraph) :
    jsf_PlanarCutCycleDuality P ↔ jcr_DualEulerCount P := Iff.rfl


theorem jsf_discreteJordan_of_cutCycleDuality (P : PlanarZ2Subgraph)
    (h : jsf_PlanarCutCycleDuality P) : DiscreteJordanSeparation P :=
  jcr_discreteJordan_of_dual P h


theorem jsf_discreteJordan_iff_cutCycleDuality (P : PlanarZ2Subgraph) :
    DiscreteJordanSeparation P ↔ jsf_PlanarCutCycleDuality P :=
  jcr_discreteJordan_iff_dualEulerCount P


theorem jsf_geometricRegionCount_eq_nullity (P : PlanarZ2Subgraph)
    (h : jsf_PlanarCutCycleDuality P) :
    geometricRegionCount P = nullity P.G :=
  jcr_geometricRegionCount_eq_nullity_of_dual P h


theorem jsf_cutCycleDuality_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    jsf_PlanarCutCycleDuality P :=
  jcr_emptyGraph_dualEulerCount hG


theorem jsf_discreteJordan_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    DiscreteJordanSeparation P :=
  jsf_discreteJordan_of_cutCycleDuality P (jsf_cutCycleDuality_of_bot hG)

end Lattice
end StatMech
