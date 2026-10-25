/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality


namespace StatMech.FrontierA

open Finset Equiv

open scoped BigOperators symmDiff

variable {D E K : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


noncomputable def ribbonBoundaryCharacterCoefficient
    [Field K] (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> K) (F : Finset E) : K :=
  ∏ b : Fin (R.boundaryComponents F), (1 - character F b)


noncomputable def dualRibbonBoundaryCharacterCoefficient
    [Field K] (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> K) (Fstar : Finset E) : K :=
  ∏ b : Fin (R.boundaryComponents Fstarᶜ),
    (1 - (character Fstarᶜ b)⁻¹)


end StatMech.FrontierA
