/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.TaftConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Notation.v1.Atlas.TensorCategories.code.TaftHopfInstance
open Coalgebra HopfAlgebra
open scoped TensorProduct


namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

/-- Bundle of Hopf-algebra data for the concrete Taft algebra: the dimension constraint
`n ≥ 2`, the primitive root-of-unity hypothesis on `q`, the defining relations on `g` and `x`,
and existence of compatible comultiplication, counit and antipode satisfying all Hopf axioms
together with their action on the generators. -/
class TaftHopfData : Prop where
  hn2 : n ≥ 2
  hq_prim : IsPrimitiveRoot q n
  gen_g_pow_n : gen_g (k := k) (q := q) hn2 ^ n = (1 : A)
  gen_x_pow_n : gen_x (k := k) (q := q) hn2 ^ n = (0 : A)
  gen_gx_comm : gen_g (k := k) (q := q) hn2 * gen_x hn2 =
    algebraMap k A q * (gen_x hn2 * gen_g hn2)
  hopf_axioms :
    ∃ (Δ : A →ₗ[k] A ⊗[k] A)
      (ε : A →ₗ[k] k)
      (S : A →ₗ[k] A),

    ((TensorProduct.assoc k A A A).toLinearMap ∘ₗ
      Δ.rTensor A ∘ₗ Δ = Δ.lTensor A ∘ₗ Δ) ∧
    (ε.rTensor A ∘ₗ Δ = TensorProduct.mk k k A 1) ∧
    (ε.lTensor A ∘ₗ Δ = (TensorProduct.mk k A k).flip 1) ∧

    (Δ 1 = 1) ∧
    (∀ a b, Δ (a * b) = Δ a * Δ b) ∧
    (ε 1 = 1) ∧
    (∀ a b, ε (a * b) = ε a * ε b) ∧

    (LinearMap.mul' k A ∘ₗ S.rTensor A ∘ₗ Δ =
      Algebra.linearMap k A ∘ₗ ε) ∧
    (LinearMap.mul' k A ∘ₗ S.lTensor A ∘ₗ Δ =
      Algebra.linearMap k A ∘ₗ ε) ∧

    (Δ (gen_g hn2) = gen_g hn2 ⊗ₜ[k] gen_g hn2) ∧
    (Δ (gen_x hn2) = gen_x hn2 ⊗ₜ[k] gen_g hn2 + 1 ⊗ₜ[k] gen_x hn2) ∧

    (ε (gen_g hn2) = (1 : k)) ∧
    (ε (gen_x hn2) = (0 : k)) ∧

    (S (gen_g hn2) = gen_g hn2 ^ (n - 1)) ∧
    (S (gen_x hn2) = -(gen_g hn2 ^ (n - 1) * gen_x hn2))

end TaftAlgebraType
