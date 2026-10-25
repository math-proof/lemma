/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.EllipticCurves.code.ECDLP.Part2


section Example_9_1

variable [Module (ZMod N) G]

variable [Module (ZMod N) G]

/-- A triple is distinguished when its `γ`-component is flagged by `B`. -/
def PollardRhoTriple.IsDistinguished
    (dpCfg : PollardRhoDPConfig G N) (t : PollardRhoTriple N G) : Prop :=
  dpCfg.B t.γ = true

/-- Two distinguished-point triples are a "DP collision" when both are distinguished
and have the same `γ` (only then does the algorithm record a useful collision). -/
def PollardRhoDPConfig.IsCollision
    (dpCfg : PollardRhoDPConfig G N)
    (t₁ t₂ : PollardRhoTriple N G) : Prop :=
  t₁.IsDistinguished dpCfg ∧ t₂.IsDistinguished dpCfg ∧ t₁.γ = t₂.γ

end Example_9_1
