/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.TaftConcrete
import Lemma.Category.Atlas.v1.TensorCategories.code.TaftConcrete
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebraExamples

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

set_option checkBinderAnnotations false in
variable [TaftHopfData k n q]

noncomputable section


/-- Extract the inequality `n ≥ 2` from `TaftHopfData`. -/
def hn2' [TaftHopfData k n q] : n ≥ 2 :=
  TaftHopfData.hn2 (k := k) (q := q)

/-- The comultiplication on the Taft algebra extracted from the existential `hopf_axioms`. -/
def taftComulLM [TaftHopfData k n q] : A →ₗ[k] A ⊗[k] A :=
  (TaftHopfData.hopf_axioms (k := k) (n := n) (q := q)).choose

/-- The counit on the Taft algebra extracted from `hopf_axioms`. -/
def taftCounitLM [TaftHopfData k n q] : A →ₗ[k] k :=
  (TaftHopfData.hopf_axioms (k := k) (n := n) (q := q)).choose_spec.choose

/-- The antipode on the Taft algebra extracted from `hopf_axioms`. -/
def taftAntipodeLM [TaftHopfData k n q] : A →ₗ[k] A :=
  (TaftHopfData.hopf_axioms (k := k) (n := n) (q := q)).choose_spec.choose_spec.choose

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

/-- The Taft algebra carries a `CoalgebraStruct` via the extracted `taftComulLM` and
`taftCounitLM`. -/
noncomputable instance taftCoalgebraStruct [TaftHopfData k n q] :
    CoalgebraStruct k A where
  comul := taftComulLM k n q
  counit := taftCounitLM k n q

/-- The instance-level comultiplication on `A` agrees with `taftComulLM`. -/
@[simp] lemma taft_comul_is [TaftHopfData k n q] :
    (CoalgebraStruct.comul : A →ₗ[k] _) = taftComulLM k n q := rfl

/-- The instance-level counit on `A` agrees with `taftCounitLM`. -/
@[simp] lemma taft_counit_is [TaftHopfData k n q] :
    (CoalgebraStruct.counit : A →ₗ[k] k) = taftCounitLM k n q := rfl

/-- The Taft algebra is a coalgebra over `k`. -/
noncomputable instance taftCoalgebra [TaftHopfData k n q] :
    Coalgebra k A where
  coassoc := taft_coassoc k n q
  rTensor_counit_comp_comul := taft_rTensor_counit k n q
  lTensor_counit_comp_comul := taft_lTensor_counit k n q

/-- The Taft algebra is a bialgebra over `k`, built from compatible algebra and coalgebra
structures. -/
noncomputable instance taftBialgebra [TaftHopfData k n q] :
    Bialgebra k A :=
  Bialgebra.mk' k A
    (show taftCounitLM k n q (1 : A) = 1 from taft_counit_one k n q)
    (fun {a b} => show taftCounitLM k n q (a * b) = taftCounitLM k n q a * taftCounitLM k n q b
      from taft_counit_mul k n q a b)
    (show taftComulLM k n q (1 : A) = 1 from taft_comul_one k n q)
    (fun {a b} => show taftComulLM k n q (a * b) = taftComulLM k n q a * taftComulLM k n q b
      from taft_comul_mul k n q a b)

/-- `HopfAlgebraStruct k A` providing the antipode via `taftAntipodeLM`. -/
noncomputable instance taftHopfAlgebraStruct [TaftHopfData k n q] :
    HopfAlgebraStruct k A where
  antipode := taftAntipodeLM k n q

/-- The instance-level antipode on `A` agrees with `taftAntipodeLM`. -/
@[simp] lemma taft_antipode_is [TaftHopfData k n q] :
    (HopfAlgebraStruct.antipode (R := k) : A →ₗ[k] _) =
      taftAntipodeLM k n q := rfl

/-- The Taft algebra is a Hopf algebra over `k`. -/
noncomputable instance taftHopfAlgebra [TaftHopfData k n q] :
    HopfAlgebra k A where
  mul_antipode_rTensor_comul := taft_hopf_rTensor k n q
  mul_antipode_lTensor_comul := taft_hopf_lTensor k n q

/-- The Taft algebra `TaftAlgebraType n q k` realises the abstract `TaftAlgebra` structure
on `(k, A)` with the concrete generators `g, x` and the antipode, comultiplication, counit
formulas extracted from `TaftHopfData`. -/
noncomputable instance taftAlgebraInstance [inst : TaftHopfData k n q] :
    TaftAlgebra k (TaftAlgebraType n q k) where
  n := n
  hn := inst.hn2
  q := q
  hq := inst.hq_prim
  g := gen_g (k := k) (q := q) inst.hn2
  x := gen_x (k := k) (q := q) inst.hn2
  g_pow_n := inst.gen_g_pow_n
  x_pow_n := inst.gen_x_pow_n
  gx_comm := inst.gen_gx_comm
  comul_g := by
    show taftComulLM k n q (gen_g inst.hn2) = _
    exact taft_comul_gen_g k n q
  comul_x := by
    show taftComulLM k n q (gen_x inst.hn2) = _
    exact taft_comul_gen_x k n q
  counit_g := by
    show taftCounitLM k n q (gen_g inst.hn2) = _
    exact taft_counit_gen_g k n q
  counit_x := by
    show taftCounitLM k n q (gen_x inst.hn2) = _
    exact taft_counit_gen_x k n q
  antipode_g := by
    show taftAntipodeLM k n q (gen_g inst.hn2) = _
    exact taft_antipode_gen_g k n q
  antipode_x := by
    show taftAntipodeLM k n q (gen_x inst.hn2) = _
    exact taft_antipode_gen_x k n q
  finrank_eq := by rw [finrank_eq]; ring

end

end TaftAlgebraType
