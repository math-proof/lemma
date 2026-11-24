module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalEndpoint
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Def.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Matrix BigOperators


@[simp] theorem ons_fin3_univ :
    (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
  decide


end StatMech.Onsager
