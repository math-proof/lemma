/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
import Def.v1.Atlas.Buildings.code.CoxeterGroup.BruhatOrder


namespace CoxeterBruhat

variable {B : Type*}

/-- Abstract hypothesis that the reflection $t$ realizing a Bruhat cover $v \lessdot w = vt$
must equal a simple reflection $s_i$ when $i$ is a descent of $w$ but not of $v$. -/
structure ReflectionIdentificationHyp {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) where
  identify : ∀ (v w : W) (t : W),
    t ∈ reflections M cs → v * t = w →
    cs.length v + 1 = cs.length w →
    ∀ (i : B), ¬cs.IsRightDescent v i → cs.IsRightDescent w i →
    t = cs.simple i

end CoxeterBruhat
