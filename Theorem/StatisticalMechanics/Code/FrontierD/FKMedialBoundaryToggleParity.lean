/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity
open Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


theorem fkMedialBlackDart0_ne_dart1 (v : T.Vertex) :
    fkMedialBlackDart0 v ≠ fkMedialBlackDart1 v := by
  intro h
  have hs := congrArg (fun d : FKMedialBlackDart T => d.1.2) h
  by_cases hp : fkMedialVertexParity v <;>
    simp [fkMedialBlackDart0, fkMedialBlackDart1, hp] at hs


end StatMech.FrontierD
