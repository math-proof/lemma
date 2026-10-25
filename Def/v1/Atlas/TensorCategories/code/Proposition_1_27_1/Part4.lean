/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_27_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Abbrev.v1.Atlas.TensorCategories.code.Proposition_1_27_1
universe u


noncomputable section

namespace EGNO.Prop1271

section Proof

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

def ext1ToSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h → SkewQuot (k := k) g h :=
  Quotient.lift
    (fun E => Submodule.Quotient.mk (p := Submodule.comap
      (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))
      ⟨E.x, E.skew_prim⟩)
    (by
      intro E₁ E₂ (hE : ComoduleExtension.Equiv E₁ E₂)
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      simp only [Submodule.subtype_apply, Submodule.coe_sub]
      exact hE)

def skewQuotToExt1 {g h : C} :
    SkewQuot (k := k) g h → ComoduleExt1 (k := k) g h :=
  Quotient.lift
    (fun (p : skewPrimitiveSpace (R := k) g h) =>
      @Quotient.mk _ (ComoduleExtension.setoid (k := k) g h) ⟨p.val, p.property⟩)
    (by
      intro a b hab
      apply Quotient.sound
      show ComoduleExtension.Equiv _ _
      unfold ComoduleExtension.Equiv; simp only
      have hab' : a - b ∈ Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
          (trivialSkewPrimitiveSubspace (k := k) g h) :=
        (Submodule.quotientRel_def _).mp hab
      rw [Submodule.mem_comap] at hab'
      simp only [Submodule.subtype_apply, Submodule.coe_sub] at hab'
      exact hab')

/-- The canonical bijection between `ComoduleExt1 g h` and the quotient
`Prim_{g,h}(C)/k(h-g)`. -/
def ext1EquivSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h ≃ SkewQuot (k := k) g h where
  toFun := ext1ToSkewQuot
  invFun := skewQuotToExt1
  left_inv := by
    intro q; induction q using Quotient.inductionOn with
    | h E => simp only [ext1ToSkewQuot, skewQuotToExt1]; rfl
  right_inv := by
    intro q; induction q using Quotient.inductionOn with
    | h p => simp only [ext1ToSkewQuot, skewQuotToExt1]; rfl

end Proof
end EGNO.Prop1271
end
