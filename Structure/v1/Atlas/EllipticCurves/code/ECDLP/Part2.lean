/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.ECDLP.Part3


section Example_9_1

variable [Module (ZMod N) G]

/-- Configuration for Pollard-ρ with distinguished points (Algorithm 9.6): extends
`PollardRhoConfig` with a boolean predicate `B : G → Bool` identifying distinguished
group elements that get logged for collision detection. -/
structure PollardRhoDPConfig (G : Type*) [AddCommGroup G] (N : ℕ) [NeZero N]
    extends PollardRhoConfig G N where
  B : G → Bool

end Example_9_1
