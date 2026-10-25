/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
open Finset
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamZeroProb
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (s : ConfigSpace V) : Real :=
  wJ E J (fun _ => 0) s / ZJ E J (fun _ => 0)

end StatMech.FrontierA
