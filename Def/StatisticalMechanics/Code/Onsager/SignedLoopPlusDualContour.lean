/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

def ons_plusDualContour (n : Nat)
    (tau : {x // x ∈ box 2 n} → Bool) : Finset (Sym2 (Site 2)) :=
  (ons_fvCutEdges (bondFinsetTouch 2 n) (glue (plusField 2) tau)).image
    flankFacesSym


end
end StatMech.Onsager
