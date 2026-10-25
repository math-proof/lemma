/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.CoxeterGroup.BruhatOrder
set_option maxHeartbeats 400000

variable {B : Type*}


namespace CoxeterBruhat

section SEC

variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The Strong Exchange Condition: if $\omega$ is a reduced word for $w$ and
$t$ is a reflection such that $\ell(wt) < \ell(w)$, then $wt$ is obtained from
$\omega$ by deleting one letter. -/
def StrongExchangeCondition
    {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) : Prop :=
  ∀ (ω : List B) (t : W),
    cs.IsReduced ω →
    t ∈ reflections M cs →
    cs.length (cs.wordProd ω * t) < cs.length (cs.wordProd ω) →
    ∃ i : Fin ω.length, cs.wordProd (ω.eraseIdx i) = cs.wordProd ω * t

/-- The reduced sublist property: every word $\omega$ admits a reduced sublist
$\tau$ with the same product. This is equivalent to the deletion condition. -/
def ReducedSublistProperty
    {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) : Prop :=
  ∀ (ω : List B), ∃ τ : List B,
    τ.Sublist ω ∧ cs.IsReduced τ ∧ cs.wordProd τ = cs.wordProd ω

end SEC

/-- The strict Bruhat order: $v < w$ iff $v \le w$ and $v \ne w$. -/
def BruhatLT (v w : W) : Prop := BruhatLE cs v w ∧ v ≠ w

end CoxeterBruhat
