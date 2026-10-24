/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/JordanCyclicBasis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.ToLin
import sympy.atlas.v1.Atlas.AlgebraNotes.code.JordanForm

namespace JordanForm

open Polynomial AdjoinRoot Matrix

variable {F : Type*} [Field F] [DecidableEq F]
