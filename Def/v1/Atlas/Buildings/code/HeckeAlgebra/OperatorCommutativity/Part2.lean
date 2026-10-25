/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Lemma.List.Any_And_IsReduced_EraseIdx.of.LtLengthMulWordProdSimple_Length_WordProd.IsReduced
import Lemma.Int.LengthMulMulSimpleSimple.gt.LengthMulSimple.of.GtLengthMul_Simple_Length.LtLengthMulSimple_Length
import Def.v1.Atlas.Buildings.code.HeckeAlgebra.Generic.Part2
import Structure.v1.Atlas.Buildings.code.HeckeAlgebra.OperatorCommutativity
open scoped Classical


namespace HeckeAlgebra

variable {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {R : Type*} [CommRing R]


/-- Converts a `FreeModuleHeckeData` into a `GenericAlgebra`: the quadratic relation
is derived from the left length-down rule applied at $w = s$. -/
def FreeModuleHeckeData.toGenericAlgebra (D : FreeModuleHeckeData M' R') :
    GenericAlgebra M' R' where
  carrier := D.carrier
  basis := D.basis
  smul := D.smul
  mul := D.mul
  add := D.add
  sc := ⟨D.a, D.b⟩
  length_up := D.left_length_up
  quadratic := by
    intro _cs s
    have h : M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * M'.toCoxeterSystem.simple s) <
        M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s) := by
      rw [M'.toCoxeterSystem.simple_mul_simple_self s,
          M'.toCoxeterSystem.length_one, M'.toCoxeterSystem.length_simple]
      omega
    have key := D.left_length_down s (M'.toCoxeterSystem.simple s) h
    rw [M'.toCoxeterSystem.simple_mul_simple_self s] at key
    exact key
  identity_left := D.identity_left
  identity_right := D.identity_right
  mul_add_right := D.mul_add_right
  mul_add_left := D.mul_add_left
  mul_smul_right := D.mul_smul_right
  smul_mul_left := D.smul_mul_left
  gen_left_assoc := D.gen_left_assoc
  gen_right_assoc := D.gen_right_assoc
  basis_span := D.basis_span

end HeckeAlgebra
