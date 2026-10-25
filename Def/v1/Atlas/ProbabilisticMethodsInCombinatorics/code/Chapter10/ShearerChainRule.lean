/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerChainRule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerEntropy
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerEntropy
open Finset BigOperators ShannonEntropy Real


namespace ShearerEntropy

variable {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Canonical equivalence between functions `Fin n → Ω` and functions from the subtype of the
universal finset to `Ω`. -/
noncomputable def funUnivEquiv (n : ℕ) (Ω : Type*) :
    (Fin n → Ω) ≃ (↥(Finset.univ : Finset (Fin n)) → Ω) where
  toFun := fun x i => x i.val
  invFun := fun f i => f ⟨i, Finset.mem_univ i⟩
  left_inv := fun x => by funext i; simp
  right_inv := fun f => by funext ⟨i, _⟩; simp

end ShearerEntropy
