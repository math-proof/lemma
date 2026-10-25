/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordanCyclic
import Def.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part3
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_contourEdgeRelaxedLocal_not_strict_of_exposed_not_source
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {f g : Site 2}
    (hexposed : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hsource : ¬ rlc_boundarySourceLocallySupported G
      (sharedPrimalEdge f g)) :
    rlc_contourEdgeRelaxedLocal G f g ∧
      ¬ rlc_contourEdgeLocal G f g := by
  refine ⟨Or.inl hexposed, ?_⟩
  rintro ⟨_htarget, hsource'⟩
  exact hsource hsource'


end Universality
end StatMech
