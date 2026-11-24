module
public import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
public import Theorem.StatisticalMechanics.Code.FrontierA.InequalitiesMenger.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Walls

variable {V : Type*} [Fintype V]


noncomputable def vertexDisjointPathNumber (G : SimpleGraph V) (A B : Set V) : ℕ :=
  (finiteABPackingSizes G A B).sup' (finiteABPackingSizes_nonempty G A B) Fin.val


end StatMech.FrontierA
