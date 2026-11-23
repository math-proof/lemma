/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimCosine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
public import Theorem.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 800000

public section

example := @kronecker_eigenvalue_cos

