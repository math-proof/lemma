/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsClean.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
public import Structure.v1.Atlas.TensorCategories.code.IntegralsClean

@[expose] public section

set_option autoImplicit false

universe u v


namespace Def1521

variable (k : Type u) [CommRing k]

/-- Named alias for Definition 1.52.1 (left integrals in an algebra with counit). -/
def Def_1_52_1_IsLeftIntegral := @IsLeftIntegral

/-- Named alias for Definition 1.52.1 (right integrals in an algebra with counit). -/
def Def_1_52_1_IsRightIntegral := @IsRightIntegral

end Def1521
