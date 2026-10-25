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
import Def.v1.Atlas.TensorCategories.code.TaftHopfInstance
open Coalgebra HopfAlgebra
open scoped TensorProduct


namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

variable [TaftHopfData k n q]

noncomputable section

/-- The full bundle of Hopf-algebra axioms satisfied by the extracted `taftComulLM`,
`taftCounitLM`, and `taftAntipodeLM`: coassociativity, counit conditions, multiplicativity,
antipode conditions, and the explicit action on the generators `g, x`. -/
lemma taft_all_axioms [TaftHopfData k n q] :
    let g := gen_g (k := k) (q := q) (hn2' k n q)
    let x := gen_x (k := k) (q := q) (hn2' k n q)
    ((TensorProduct.assoc k A A A).toLinearMap ∘ₗ
      (taftComulLM k n q).rTensor A ∘ₗ taftComulLM k n q =
      (taftComulLM k n q).lTensor A ∘ₗ taftComulLM k n q) ∧
    ((taftCounitLM k n q).rTensor A ∘ₗ taftComulLM k n q =
      TensorProduct.mk k k A 1) ∧
    ((taftCounitLM k n q).lTensor A ∘ₗ taftComulLM k n q =
      (TensorProduct.mk k A k).flip 1) ∧
    (taftComulLM k n q (1 : A) = 1) ∧
    (∀ a b, taftComulLM k n q (a * b) = taftComulLM k n q a * taftComulLM k n q b) ∧
    (taftCounitLM k n q (1 : A) = 1) ∧
    (∀ a b, taftCounitLM k n q (a * b) = taftCounitLM k n q a * taftCounitLM k n q b) ∧
    (LinearMap.mul' k A ∘ₗ (taftAntipodeLM k n q).rTensor A ∘ₗ
      taftComulLM k n q = Algebra.linearMap k A ∘ₗ taftCounitLM k n q) ∧
    (LinearMap.mul' k A ∘ₗ (taftAntipodeLM k n q).lTensor A ∘ₗ
      taftComulLM k n q = Algebra.linearMap k A ∘ₗ taftCounitLM k n q) ∧
    (taftComulLM k n q g = g ⊗ₜ[k] g) ∧
    (taftComulLM k n q x = x ⊗ₜ[k] g + 1 ⊗ₜ[k] x) ∧
    (taftCounitLM k n q g = (1 : k)) ∧
    (taftCounitLM k n q x = (0 : k)) ∧
    (taftAntipodeLM k n q g = g ^ (n - 1)) ∧
    (taftAntipodeLM k n q x = -(g ^ (n - 1) * x)) :=
  (TaftHopfData.hopf_axioms (k := k) (n := n) (q := q)).choose_spec.choose_spec.choose_spec

/-- Coassociativity of the Taft comultiplication. -/
lemma taft_coassoc [TaftHopfData k n q] :
    (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
      (taftComulLM k n q).rTensor A ∘ₗ taftComulLM k n q =
      (taftComulLM k n q).lTensor A ∘ₗ taftComulLM k n q :=
  (taft_all_axioms k n q).1

/-- Right counit axiom for the Taft Hopf algebra. -/
lemma taft_rTensor_counit [TaftHopfData k n q] :
    (taftCounitLM k n q).rTensor A ∘ₗ taftComulLM k n q =
      TensorProduct.mk k k A 1 :=
  (taft_all_axioms k n q).2.1

/-- Left counit axiom for the Taft Hopf algebra. -/
lemma taft_lTensor_counit [TaftHopfData k n q] :
    (taftCounitLM k n q).lTensor A ∘ₗ taftComulLM k n q =
      (TensorProduct.mk k A k).flip 1 :=
  (taft_all_axioms k n q).2.2.1

/-- The Taft comultiplication preserves `1`: `Δ(1) = 1 ⊗ 1`. -/
lemma taft_comul_one [TaftHopfData k n q] :
    taftComulLM k n q (1 : A) = 1 :=
  (taft_all_axioms k n q).2.2.2.1

/-- The Taft comultiplication is multiplicative. -/
lemma taft_comul_mul [TaftHopfData k n q] (a b : A) :
    taftComulLM k n q (a * b) = taftComulLM k n q a * taftComulLM k n q b :=
  (taft_all_axioms k n q).2.2.2.2.1 a b

/-- The Taft counit sends `1 ∈ A` to `1 ∈ k`. -/
lemma taft_counit_one [TaftHopfData k n q] :
    taftCounitLM k n q (1 : A) = 1 :=
  (taft_all_axioms k n q).2.2.2.2.2.1

/-- The Taft counit is multiplicative. -/
lemma taft_counit_mul [TaftHopfData k n q] (a b : A) :
    taftCounitLM k n q (a * b) = taftCounitLM k n q a * taftCounitLM k n q b :=
  (taft_all_axioms k n q).2.2.2.2.2.2.1 a b

/-- Right Hopf axiom: `μ ∘ (S ⊗ id) ∘ Δ = η ∘ ε`. -/
lemma taft_hopf_rTensor [TaftHopfData k n q] :
    LinearMap.mul' k A ∘ₗ
      (taftAntipodeLM k n q).rTensor A ∘ₗ taftComulLM k n q =
      Algebra.linearMap k A ∘ₗ taftCounitLM k n q :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.1

/-- Left Hopf axiom: `μ ∘ (id ⊗ S) ∘ Δ = η ∘ ε`. -/
lemma taft_hopf_lTensor [TaftHopfData k n q] :
    LinearMap.mul' k A ∘ₗ
      (taftAntipodeLM k n q).lTensor A ∘ₗ taftComulLM k n q =
      Algebra.linearMap k A ∘ₗ taftCounitLM k n q :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.2.1

/-- `Δ(g) = g ⊗ g`: the generator `g` is grouplike. -/
lemma taft_comul_gen_g [TaftHopfData k n q] :
    taftComulLM k n q (gen_g (k := k) (q := q) (hn2' k n q)) =
      gen_g (hn2' k n q) ⊗ₜ[k] gen_g (hn2' k n q) :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.2.2.1

/-- `Δ(x) = x ⊗ g + 1 ⊗ x`: the generator `x` is `(1, g)`-skew-primitive. -/
lemma taft_comul_gen_x [TaftHopfData k n q] :
    taftComulLM k n q (gen_x (k := k) (q := q) (hn2' k n q)) =
      gen_x (hn2' k n q) ⊗ₜ[k] gen_g (hn2' k n q) +
      1 ⊗ₜ[k] gen_x (hn2' k n q) :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.2.2.2.1

/-- The counit sends `g` to `1`. -/
lemma taft_counit_gen_g [TaftHopfData k n q] :
    taftCounitLM k n q (gen_g (k := k) (q := q) (hn2' k n q)) = (1 : k) :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.2.2.2.2.1

/-- The counit sends `x` to `0`. -/
lemma taft_counit_gen_x [TaftHopfData k n q] :
    taftCounitLM k n q (gen_x (k := k) (q := q) (hn2' k n q)) = (0 : k) :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `S(g) = g^{n-1} = g⁻¹`. -/
lemma taft_antipode_gen_g [TaftHopfData k n q] :
    taftAntipodeLM k n q (gen_g (k := k) (q := q) (hn2' k n q)) =
      gen_g (hn2' k n q) ^ (n - 1) :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `S(x) = -(g^{n-1} * x) = -(g⁻¹ * x)`. -/
lemma taft_antipode_gen_x [TaftHopfData k n q] :
    taftAntipodeLM k n q (gen_x (k := k) (q := q) (hn2' k n q)) =
      -(gen_g (hn2' k n q) ^ (n - 1) * gen_x (hn2' k n q)) :=
  (taft_all_axioms k n q).2.2.2.2.2.2.2.2.2.2.2.2.2.2

end
end TaftAlgebraType
