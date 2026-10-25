/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jeb_faithfulDiscreteJordan_of_residue (hres : jeb_FaithfulCountResidue)
    (P : PlanarZ2Subgraph) (hP : jeb_EvenDegreeSubgraph P) :
    whc_FaithfulDiscreteJordan P :=
  hres P hP


theorem jeb_unitSquare_interior_bounded :
    Nonempty {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite} :=
  ⟨⟨(whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0],
    whb_faceRegion_interior_bounded⟩⟩


theorem jeb_Htest_le : whc_Htest ≤ hypercubicLattice 2 := fun a b hab =>
  imageGraph_le_lattice jbc_Pce (SimpleGraph.deleteEdges_le _ hab)


end Lattice
end StatMech
