/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Instance.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

noncomputable def ons_plusDualFaceEdgeLift (n : Nat)
    (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
    Sym2 (ons_PlusDualFaceVertex n) :=
  s(⟨edge.1.out.1, edge.2.2 edge.1.out.1 (Sym2.out_fst_mem edge.1)⟩,
    ⟨edge.1.out.2, edge.2.2 edge.1.out.2 (Sym2.out_snd_mem edge.1)⟩)

end
end StatMech.Onsager
