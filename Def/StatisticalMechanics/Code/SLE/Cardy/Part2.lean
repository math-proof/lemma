/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Structure.StatisticalMechanics.Code.SLE.Cardy

@[expose] public section

open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

def Mobius.apply {K : Type*} [Field K] (m : Mobius K) (z : K) : K :=
  (m.a * z + m.b) / (m.c * z + m.d)


def Mobius.id (K : Type*) [Field K] : Mobius K where
  a := 1; b := 0; c := 0; d := 1
  det_ne_zero := by simp

end StatMech.SLE
