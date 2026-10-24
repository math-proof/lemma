/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeGeneratorIdentity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.Roots

open CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]
