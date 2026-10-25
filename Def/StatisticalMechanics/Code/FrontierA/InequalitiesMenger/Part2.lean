/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.InequalitiesMenger
open Finset SimpleGraph


namespace StatMech.FrontierA

open Walls

variable {V : Type*} [Fintype V]


noncomputable def vertexSeparatorNumber (G : SimpleGraph V) (A B : Set V) : ℕ :=
  (finiteABSeparators G A B).inf' (finiteABSeparators_nonempty G A B) Finset.card


noncomputable def finiteABPackingSizes (G : SimpleGraph V) (A B : Set V) :
    Finset (Fin (Fintype.card V + 1)) := by
  classical
  exact Finset.univ.filter fun k =>
    Nonempty (bc16_DisjointPathFamily G A B (Fin k.val))

end StatMech.FrontierA
