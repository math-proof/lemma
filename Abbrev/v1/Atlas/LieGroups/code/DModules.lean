/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie
import Def.v1.Atlas.LieGroups.code.DModules.Part4
universe u v w


namespace DModules

open scoped TensorProduct

section DirectInverseImage

noncomputable abbrev TransferBimodule
    (OY : Type u) [CommRing OY]
    (OX : Type v) [CommRing OX] [Algebra OY OX]
    (DY : Type w) [AddCommGroup DY] [Module OY DY] :
    Type (max v w) :=
  TensorProduct OY OX DY

noncomputable abbrev inverseImageModule
    (OY : Type u) [CommRing OY]
    (OX : Type v) [CommRing OX] [Algebra OY OX]
    (N : Type w) [AddCommGroup N] [Module OY N] :
    Type (max v w) :=
  TensorProduct OY OX N

noncomputable abbrev directImageModule
    (OY : Type u) [CommRing OY]
    (OX : Type v) [CommRing OX] [Algebra OY OX]
    (DY : Type w) [AddCommGroup DY] [Module OY DY]
    (M : Type x) [AddCommGroup M] [Module OX M] :
    Type (max x v w) :=
  TensorProduct OX M (TransferBimodule OY OX DY)

end DirectInverseImage
end DModules
