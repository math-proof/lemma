/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma5


namespace StatMech.Onsager

open Matrix BigOperators


theorem ons_mem_loopSetBoth {E} [Fintype E] [DecidableEq E] {n : ℕ}
    (a b : E) (v : Fin n → E) :
    v ∈ ons_loopSetBoth (n := n) a b ↔ (∃ i, v i = a) ∧ (∃ j, v j = b) := by
  unfold ons_loopSetBoth
  simp


theorem ons_lemma5_of_involution {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (g : (Fin n → E) → (Fin n → E))
    (hmaps : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g v ∈ ons_loopSetBoth (n := n) e (rev e))
    (hsign : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e),
      ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
    (hinv : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g (g v) = v)
    (hne : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g v ≠ v) :
    ∑ v ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight Λ v = 0 :=
  ons_sum_zero_of_sign_involution Λ (ons_loopSetBoth (n := n) e (rev e)) g hmaps hsign hinv hne


end StatMech.Onsager
