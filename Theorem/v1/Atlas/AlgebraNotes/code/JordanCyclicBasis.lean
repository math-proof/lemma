/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/JordanCyclicBasis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Def.v1.Atlas.AlgebraNotes.code.JordanForm

public section

namespace JordanForm

open Polynomial AdjoinRoot Matrix

variable {F : Type*} [Field F] [DecidableEq F]

end JordanForm
