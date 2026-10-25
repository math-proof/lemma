/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ReflectionIdentificationGenuine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.CoxeterGroup.StrongExchangeProof
set_option linter.unusedSectionVars false


namespace CoxeterReflectionId

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Hypothesis bridge for identifying reflections from inversion-set differences:
if $vt = w$ with $\ell(v) + 1 = \ell(w)$ and a generator $i$ flips its descent status,
then $t$ equals the simple reflection $s_i$. -/
structure InversionDifferenceBridgeHyp {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) where
  identify_from_inversions : ∀ (v w : W) (t : W),
    t ∈ CoxeterBruhat.reflections M cs → v * t = w →
    cs.length v + 1 = cs.length w →
    ∀ (i : B), ¬cs.IsRightDescent v i → cs.IsRightDescent w i →
    t = cs.simple i

end CoxeterReflectionId
