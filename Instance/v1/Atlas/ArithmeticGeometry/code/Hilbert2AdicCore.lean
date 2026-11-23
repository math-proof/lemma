/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
public import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
@[expose] public section

open PadicInt HilbertSymbol


instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_one_dec u₀ v₀) :=
  inferInstance

instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_two_dec u₀ v₀) :=
  inferInstance

