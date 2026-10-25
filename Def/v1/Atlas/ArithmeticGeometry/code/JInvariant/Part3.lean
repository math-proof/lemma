/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.TateShafarevich.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.TateShafarevich
import Instance.v1.Atlas.ArithmeticGeometry.code.JInvariant


noncomputable section

universe u

open WeierstrassCurve

namespace shortWeierstrassCurve

variable {R : Type*} [CommRing R] (a₄ a₆ : R)

/-- The $j$-invariant $j(C) \in k$ of a genus-one curve $C$, defined as the
$j$-invariant of its Jacobian. -/
def GenusOneCurve.jInvariant {k : Type u} [Field k] (C : GenusOneCurve k) : k :=
  C.Jacobian.jInvariant

end shortWeierstrassCurve
end
