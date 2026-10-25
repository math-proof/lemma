/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part2


namespace StatMech.FrontierA

theorem crossCollision_fst_injective
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C) :
    Function.Injective fun collision : crossCollision f g => collision.1.1 := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext hxy
  apply g.injective
  calc
    g x.1.2 = f x.1.1 := x.2.symm
    _ = f y.1.1 := congrArg f hxy
    _ = g y.1.2 := y.2

theorem crossCollision_snd_injective
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C) :
    Function.Injective fun collision : crossCollision f g => collision.1.2 := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · apply f.injective
    calc
      f x.1.1 = g x.1.2 := x.2
      _ = g y.1.2 := congrArg g hxy
      _ = f y.1.1 := y.2.symm
  · exact hxy


end StatMech.FrontierA
