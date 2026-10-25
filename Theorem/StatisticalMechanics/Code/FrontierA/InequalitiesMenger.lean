/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Def.StatisticalMechanics.Code.FrontierA.InequalitiesMenger
open Finset SimpleGraph


namespace StatMech.FrontierA

open Walls

variable {V : Type*} [Fintype V]


theorem finiteABSeparators_nonempty (G : SimpleGraph V) (A B : Set V) :
    (finiteABSeparators G A B).Nonempty := by
  classical
  refine ⟨Finset.univ, ?_⟩
  simp only [finiteABSeparators, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using bc16_univ_isSeparator G A B


end StatMech.FrontierA
