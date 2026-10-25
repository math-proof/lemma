/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionGenuine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part4
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Roots
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
open Finset BigOperators


namespace CoxeterExchangeGenuine

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Geometric bridge hypothesis: bundles the two implications connecting the
abstract length function and the geometric representation. Field
$\mathtt{length\_decrease\_negative}$ says length-decrease on right
multiplication implies negativity of the resulting root, and field
$\mathtt{sign\_change\_exchange}$ says negativity implies the exchange
relation $\omega = \omega' \cdot s$ for some deletion of $\omega$. -/
structure GeometricBridgeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) where
  length_decrease_negative : ∀ (word : List B) (s : B),
    cs.IsReduced word →
    cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word) →
    CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word (CoxeterGroup.e s))
  sign_change_exchange : ∀ (word : List B) (s : B),
    cs.IsReduced word →
    CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word (CoxeterGroup.e s)) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s


/-- A more granular bridge hypothesis: for any reduced word $\omega$ and
simple root $e_s$ whose total geometric image is negative, an index $k$
witnessing the sign change of the $s$-coordinate yields an exchange
$\omega = \omega' \cdot s$ for some deletion of $\omega$. -/
structure RootSignChangeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) where
  sign_change_at_index : ∀ (word : List B) (s : B) (k : ℕ),
    cs.IsReduced word →
    k < word.length →

    CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word (CoxeterGroup.e s)) →

    (CoxeterGroup.wordSigma M (word.drop (word.length - k)) (CoxeterGroup.e s) s > 0) →
    (CoxeterGroup.wordSigma M (word.drop (word.length - (k + 1))) (CoxeterGroup.e s) s ≤ 0) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

end CoxeterExchangeGenuine
