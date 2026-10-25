/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.TateShafarevich.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.TateShafarevich
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant


noncomputable section

universe u

open WeierstrassCurve

namespace shortWeierstrassCurve

variable {R : Type*} [CommRing R] (a₄ a₆ : R)

/-- **Theorem 26.3 (surjectivity).** Over any field $k$, every value $j \in k$
arises as the $j$-invariant of some elliptic curve over $k$. -/
theorem j_invariant_surjective {k : Type*} [Field k] (j : k) :
    ∃ E : EllipticCurveOver k, E.jInvariant = j := by
  classical
  exact ⟨⟨WeierstrassCurve.ofJ j⟩, WeierstrassCurve.ofJ_j j⟩

end shortWeierstrassCurve
end
