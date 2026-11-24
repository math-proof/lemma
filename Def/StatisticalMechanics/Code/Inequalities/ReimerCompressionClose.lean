module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


variable {β : Type*} [Fintype β] [DecidableEq β]


noncomputable def iterDoubleCompress (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    Finset (Finset (β ⊕ β)) :=
  is.foldr doubleCompress 𝒰

end StatMech
