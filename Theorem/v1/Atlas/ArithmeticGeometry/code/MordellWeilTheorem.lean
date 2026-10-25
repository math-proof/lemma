/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MordellWeilTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Heights.Part4
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Heights
/-- Existence of the canonical (Néron-Tate) height on an elliptic curve over $\mathbb{Q}$: a function $\hat{h}$ that is nonnegative, satisfies $\hat{h}(2P) = 4\hat{h}(P)$, the parallelogram law $\hat{h}(P+Q) + \hat{h}(P-Q) = 2\hat{h}(P) + 2\hat{h}(Q)$, and the Northcott property (sublevel sets are finite). -/


namespace EllipticCurve.MordellWeil

open EllipticCurve.WeakMordellWeil CanonicalHeight

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]

end EllipticCurve.MordellWeil

noncomputable section

end
