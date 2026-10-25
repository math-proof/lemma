/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionWiring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Structure.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
open CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 800000


namespace CoxeterExchange

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The sign-change exchange hypothesis: whenever a reduced word $\omega$ makes
$e_s$ into a negative root, there is some position $i$ in $\omega$ such that
deleting it gives a word with product $\mathtt{wordProd}\,\omega \cdot
\mathtt{simple}\,s$. -/
abbrev SignChangeExchangeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B) (s : B),
    cs.IsReduced word →
    IsNegative (wordSigma M word (e s)) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

end CoxeterExchange
