/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Instance.StatisticalMechanics.Code.OSSS.Monotonic
open Finset


namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] [DecidableEq E] in

lemma agree_self (F : Finset E) (η : ConfigSpace E) : Agree F η η := fun _ _ => rfl

omit [Fintype E] [DecidableEq E] in


lemma agree_inf (F : Finset E) (ξ ζ a b : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (ha : Agree F ξ a) (hb : Agree F ζ b) :
    Agree F ξ (a ⊓ b) := by
  intro f hf
  show a f ⊓ b f = ξ f
  rw [ha f hf, hb f hf]
  exact inf_eq_left.mpr (hle f hf)

omit [Fintype E] [DecidableEq E] in


lemma agree_sup (F : Finset E) (ξ ζ a b : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (ha : Agree F ξ a) (hb : Agree F ζ b) :
    Agree F ζ (a ⊔ b) := by
  intro f hf
  show a f ⊔ b f = ζ f
  rw [ha f hf, hb f hf]
  exact sup_eq_right.mpr (hle f hf)


end OSSS.Monotonic
end StatMech
