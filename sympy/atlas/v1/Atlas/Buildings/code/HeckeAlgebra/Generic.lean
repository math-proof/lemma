/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

namespace HeckeAlgebra

variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B}

/-- The pair of scalars $(a_s, b_s)_{s ∈ B}$ defining the quadratic relation
$T_s^2 = a_s T_s + b_s T_1$ for a generic Hecke algebra. -/
structure StructureConstants (B : Type*) (R : Type*) [CommRing R] where
  a : B → R
  b : B → R

variable {R : Type*} [CommRing R]

/-- The structure constants are conjugacy-invariant if conjugate simple reflections
have equal $(a_s, b_s)$ values. -/
def StructureConstants.ConjugacyInvariant (sc : StructureConstants B R)
    (cs : CoxeterSystem M W) : Prop :=
  ∀ (s₁ s₂ : B) (w : W), w * cs.simple s₁ * w⁻¹ = cs.simple s₂ →
    sc.a s₁ = sc.a s₂ ∧ sc.b s₁ = sc.b s₂

/-- A generic Hecke algebra over $R$ for the Coxeter matrix $M$: an $R$-module
`carrier` with basis $\{T_w : w ∈ W\}$, satisfying the length-up rule
$T_s T_w = T_{sw}$ when $\ell(sw) > \ell(w)$, the quadratic relation
$T_s^2 = a_s T_s + b_s T_1$, left/right identity for $T_1$, two-sided generator
associativity, and a basis-span induction principle. -/
structure GenericAlgebra (M : CoxeterMatrix B) (R : Type*) [CommRing R] where
  carrier : Type*
  basis : M.Group → carrier
  smul : R → carrier → carrier
  mul : carrier → carrier → carrier
  add : carrier → carrier → carrier
  sc : StructureConstants B R
  length_up : let cs := M.toCoxeterSystem
    ∀ (s : B) (w : M.Group),
    cs.length (cs.simple s * w) > cs.length w →
    mul (basis (cs.simple s)) (basis w) = basis (cs.simple s * w)
  quadratic : let cs := M.toCoxeterSystem
    ∀ (s : B),
    mul (basis (cs.simple s)) (basis (cs.simple s)) =
      add (smul (sc.a s) (basis (cs.simple s)))
          (smul (sc.b s) (basis 1))
  identity_left : ∀ (x : carrier), mul (basis 1) x = x
  identity_right : ∀ (x : carrier), mul x (basis 1) = x
  mul_add_right : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_add_left : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  mul_smul_right : ∀ (r : R) x y, mul x (smul r y) = smul r (mul x y)
  smul_mul_left : ∀ (r : R) x y, mul (smul r x) y = smul r (mul x y)
  gen_left_assoc : let cs := M.toCoxeterSystem
    ∀ (s : B) (x y : carrier),
    mul (basis (cs.simple s)) (mul x y) = mul (mul (basis (cs.simple s)) x) y
  gen_right_assoc : let cs := M.toCoxeterSystem
    ∀ (t : B) (x y : carrier),
    mul (mul x y) (basis (cs.simple t)) = mul x (mul y (basis (cs.simple t)))
  basis_span : ∀ (P : carrier → Prop),
    (∀ w, P (basis w)) →
    (∀ x y, P x → P y → P (add x y)) →
    (∀ (r : R) x, P x → P (smul r x)) →
    ∀ z, P z


section CoxeterLemmas

variable {M : CoxeterMatrix B}

/-- Data of an Iwahori–Hecke specialization: parameters $q_s$ for each simple
reflection $s$. -/
structure IwahoriHeckeData (B : Type*) (R : Type*) [CommRing R] where
  q : B → R

/-- Converts Iwahori–Hecke parameters $q_s$ into the generic structure constants
$(a_s, b_s) = (q_s - 1, q_s)$. -/
def IwahoriHeckeData.toStructureConstants (d : IwahoriHeckeData B R) :
    StructureConstants B R where
  a s := d.q s - 1
  b s := d.q s

end HeckeAlgebra
