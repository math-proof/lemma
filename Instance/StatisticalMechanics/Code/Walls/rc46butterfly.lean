module
public import Theorem.StatisticalMechanics.Code.Walls.rc45doubledcover.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
public import Def.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


instance : DecidablePred rc46_isComplementary := fun _ => by unfold rc46_isComplementary; infer_instance


end StatMech.Walls
