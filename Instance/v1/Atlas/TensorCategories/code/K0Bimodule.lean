/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Opposite
import Structure.v1.Atlas.TensorCategories.code.K0Bimodule
set_option maxHeartbeats 800000

open Finset FusionRing


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

namespace K0Group

variable {R : FusionRing ι}

/-- The zero element of `K₀(R)` is the all-zero coefficient vector. -/
instance : Zero (K0Group R) := ⟨⟨fun _ => 0⟩⟩

/-- Componentwise addition of elements of `K₀(R)`. -/
instance : Add (K0Group R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩

/-- Componentwise negation on `K₀(R)`. -/
instance : Neg (K0Group R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩

/-- Componentwise subtraction on `K₀(R)`. -/
instance : Sub (K0Group R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩

/-- Natural-number scalar multiplication on `K₀(R)`, applied componentwise. -/
instance : SMul ℕ (K0Group R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Integer scalar multiplication on `K₀(R)`, applied componentwise. -/
instance : SMul ℤ (K0Group R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

end K0Group
end FusionRing
