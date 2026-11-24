module
public import Theorem.StatisticalMechanics.Code.Walls.rc52pairimage
public import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
public import Def.StatisticalMechanics.Code.Walls.rc53butterfly.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


instance {n : ℕ} : DecidablePred (rc53_isCubeFilling (n := n)) :=
  fun _ => by unfold rc53_isCubeFilling; infer_instance


end StatMech.Walls
