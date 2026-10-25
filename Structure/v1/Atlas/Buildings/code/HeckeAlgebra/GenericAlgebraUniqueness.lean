/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/GenericAlgebraUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.HeckeAlgebra.OperatorCommutativity.Part2
import Lemma.Finsupp.LambdaLift.eq.SMul
open scoped Classical


namespace HeckeAlgebra

section Uniqueness

variable {B' : Type*} {M' : CoxeterMatrix B'} {R' : Type*} [CommRing R']

/-- Abstract data of a Hecke-algebra multiplication on `C` over $R$ with basis indexed by
$W = M.\mathrm{Group}$: the length-up product $T_s T_w = T_{sw}$ when $\ell(sw) > \ell(w)$,
the length-down product $T_s T_w = a_s T_w + b_s T_{sw}$, left-identity, distributivity,
scalar associativity, and a span principle on the basis. -/
structure HeckeMultiplication (M : CoxeterMatrix B') (R : Type*) [CommRing R]
    (C : Type*) where
  basis : M.Group → C
  smul : R → C → C
  mul : C → C → C
  add : C → C → C
  sc : StructureConstants B' R
  length_up : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) >
      M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) =
      basis (M.toCoxeterSystem.simple s * w)
  length_down : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) <
      M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) =
      add (smul (sc.a s) (basis w))
          (smul (sc.b s) (basis (M.toCoxeterSystem.simple s * w)))
  identity_left : ∀ (x : C), mul (basis 1) x = x
  mul_add_right : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_add_left : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  mul_smul_right : ∀ (r : R) x y, mul x (smul r y) = smul r (mul x y)
  smul_mul_left : ∀ (r : R) x y, mul (smul r x) y = smul r (mul x y)
  gen_left_assoc : ∀ (s : B') (x y : C),
    mul (basis (M.toCoxeterSystem.simple s)) (mul x y) =
      mul (mul (basis (M.toCoxeterSystem.simple s)) x) y
  basis_span : ∀ (P : C → Prop),
    (∀ w, P (basis w)) →
    (∀ x y, P x → P y → P (add x y)) →
    (∀ (r : R) x, P x → P (smul r x)) →
    ∀ z, P z

end Uniqueness
end HeckeAlgebra
