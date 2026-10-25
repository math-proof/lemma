/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_compresscard
open Finset
open scoped NNReal FinsetFamily


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def iterDownCompress (cs : List E) (𝒜 : Finset (ConfigSpace E)) :
    Finset (ConfigSpace E) :=
  cs.foldr downCompress 𝒜

end StatMech.Walls
