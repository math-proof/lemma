/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Structure.v1.Atlas.EllipticCurves.code.FermatsLastTheorem


noncomputable section

namespace FLT

open UniqueFactorizationMonoid

/-- The mod-`ℓ` representation of `E/ℚ` is modular of a prescribed weight and level:
there is a weight-`2` newform of the given level matching `tr ρ(Frob_p)` at primes
`p ∤ ℓ · level`. -/
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- `5` is a prime number. Provided as a `Fact` for use as a typeclass parameter. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end FLT
end
