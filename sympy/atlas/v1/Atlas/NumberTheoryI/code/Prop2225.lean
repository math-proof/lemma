/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2225.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.GlobalCFT
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22Conductor
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Ch22Conductor

noncomputable section

open NumberField RayClassField GlobalConductor KroneckerWeber

namespace ConductorRamification

universe u

variable {K : Type u} [Field K] [NumberField K]
         {L : Type u} [Field L] [NumberField L]
         [Algebra K L] [FiniteDimensional K L] [IsAbelianExtension K L]
