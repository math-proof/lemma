/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic

set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w

noncomputable section


/-- An element `g` of a coalgebra is grouplike when `Δ g = g ⊗ g` and `ε g = 1`. -/
def IsGrouplike {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g : C) : Prop :=
  Coalgebra.comul (R := R) g = g ⊗ₜ g ∧ Coalgebra.counit (R := R) g = 1

/-- An element `x` of a coalgebra is `(g, h)`-skew-primitive when its comultiplication
satisfies `Δ x = x ⊗ g + h ⊗ x`. -/
def IsSkewPrimitive {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g h x : C) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x

/-- The `R`-submodule of all `(g, h)`-skew-primitive elements of a coalgebra `C`. -/
def skewPrimitiveSpace {R : Type*} {C : Type*} [CommSemiring R] [AddCommGroup C] [Module R C]
    [Coalgebra R C] (g h : C) : Submodule R C where
  carrier := {x : C | IsSkewPrimitive (R := R) g h x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    unfold IsSkewPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


namespace HopfAlgebra

/-- An element `x` of a bialgebra is primitive when `Δ x = x ⊗ 1 + 1 ⊗ x`; equivalently, a
`(1, 1)`-skew-primitive element. -/
def IsPrimitive {R : Type*} {H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
    (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ 1 + 1 ⊗ₜ x

/-- The `R`-submodule of primitive elements of a bialgebra. -/
def primitiveElements {R : Type*} {H : Type*} [CommSemiring R] [Semiring H]
    [Bialgebra R H] : Submodule R H where
  carrier := {x : H | IsPrimitive (R := R) x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    unfold IsPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

end HopfAlgebra


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Vanishing of `Ext¹(X, Y)`: every short exact sequence `0 → Y → V → X → 0` in `C` splits. -/
def Ext1Vanishes (X Y : C) : Prop :=
  ∀ (V : C) (f : Y ⟶ V) (g : V ⟶ X) (hfg : f ≫ g = 0),
    (ShortComplex.mk f g hfg).ShortExact → Nonempty (ShortComplex.mk f g hfg).Splitting

/-- A finite `k`-linear ring category: an abelian monoidal `k`-linear category that has enough
projectives and finite-dimensional Hom-spaces. -/
class FiniteRingCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    extends MonoidalCategory C, Abelian C, Linear k C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

/-- In characteristic zero, every self-extension of the simple unit in a finite ring category
splits, i.e. `Ext¹(𝟙_C, 𝟙_C) = 0`. -/
end TensorCategories


section TrivialSkewPrimitive

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The one-dimensional subspace spanned by the trivial skew-primitive element `h - g`. -/
def trivialSkewPrimitiveSubspace (g h : C) : Submodule k C :=
  Submodule.span k {h - g}

/-- The reduced space of skew-primitives: the quotient of `skewPrimitiveSpace g h` by its trivial
sub-line, capturing genuinely nontrivial skew-primitive directions. -/
def reducedSkewPrimitiveSpace
    {g h : C} (_hg : IsGrouplike (R := k) g) (_hh : IsGrouplike (R := k) h) :
    Type u :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

end TrivialSkewPrimitive


section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A comodule extension between grouplikes `g` and `h`: a skew-primitive element witnessing a
short exact sequence `0 → k·g → V → k·h → 0` of comodules. -/
structure ComoduleExtension (g h : C) where
  x : C
  skew_prim : IsSkewPrimitive (R := k) g h x

/-- Two comodule extensions are equivalent when their witnessing skew-primitives differ by a
trivial skew-primitive multiple of `h - g`. -/
def ComoduleExtension.Equiv {g h : C} (E₁ E₂ : ComoduleExtension (k := k) g h) : Prop :=
  E₁.x - E₂.x ∈ trivialSkewPrimitiveSubspace (k := k) g h

/-- Forget a comodule extension to the underlying skew-primitive element in `skewPrimitiveSpace`. -/
def ComoduleExtension.toSkewPrimitive {g h : C} (E : ComoduleExtension (k := k) g h) :
    skewPrimitiveSpace (R := k) g h :=
  ⟨E.x, E.skew_prim⟩

/-- Convert a skew-primitive element to the corresponding comodule extension. -/
def ComoduleExtension.ofSkewPrimitive {g h : C}
    (p : skewPrimitiveSpace (R := k) g h) : ComoduleExtension (k := k) g h :=
  ⟨p.val, p.property⟩

/-- Reflexivity of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.refl {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExtension.Equiv E E := by
  unfold ComoduleExtension.Equiv
  simp [trivialSkewPrimitiveSubspace]

/-- Symmetry of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.symm {g h : C}
    {E₁ E₂ : ComoduleExtension (k := k) g h} (h_eq : ComoduleExtension.Equiv E₁ E₂) :
    ComoduleExtension.Equiv E₂ E₁ := by
  unfold ComoduleExtension.Equiv at *
  rwa [show E₂.x - E₁.x = -(E₁.x - E₂.x) from (neg_sub E₁.x E₂.x).symm, neg_mem_iff]

/-- Transitivity of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.trans {g h : C}
    {E₁ E₂ E₃ : ComoduleExtension (k := k) g h}
    (h₁₂ : ComoduleExtension.Equiv E₁ E₂) (h₂₃ : ComoduleExtension.Equiv E₂ E₃) :
    ComoduleExtension.Equiv E₁ E₃ := by
  unfold ComoduleExtension.Equiv at *
  have : E₁.x - E₃.x = (E₁.x - E₂.x) + (E₂.x - E₃.x) := by abel
  rw [this]
  exact Submodule.add_mem _ h₁₂ h₂₃

/-- The setoid structure on comodule extensions induced by the equivalence relation. -/
instance ComoduleExtension.setoid (g h : C) :
    Setoid (ComoduleExtension (k := k) g h) where
  r := ComoduleExtension.Equiv
  iseqv := {
    refl := ComoduleExtension.Equiv.refl
    symm := ComoduleExtension.Equiv.symm
    trans := ComoduleExtension.Equiv.trans
  }

/-- The space `Ext¹` of comodule extensions between grouplikes `g` and `h`, defined as
equivalence classes of comodule extensions. -/
def ComoduleExt1 (g h : C) : Type u :=
  Quotient (ComoduleExtension.setoid (k := k) g h)

/-- Form the `Ext¹` equivalence class of a comodule extension. -/
def ComoduleExt1.mk {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExt1 (k := k) g h :=
  Quotient.mk _ E

private abbrev SkewQuot (g h : C) :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

private def ext1ToSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h → SkewQuot (k := k) g h :=
  Quotient.lift
    (fun E => Submodule.Quotient.mk (p := Submodule.comap
      (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))
      ⟨E.x, E.skew_prim⟩)
    (by
      intro E₁ E₂ (hE : ComoduleExtension.Equiv E₁ E₂)
      rw [Submodule.Quotient.eq]
      rw [Submodule.mem_comap]
      simp only [Submodule.subtype_apply, Submodule.coe_sub]
      exact hE)

private def skewQuotToExt1 {g h : C} :
    SkewQuot (k := k) g h → ComoduleExt1 (k := k) g h :=
  Quotient.lift
    (fun (p : skewPrimitiveSpace (R := k) g h) =>
      ComoduleExt1.mk (k := k) (ComoduleExtension.ofSkewPrimitive (k := k) p))
    (by
      intro a b hab
      apply Quotient.sound
      show ComoduleExtension.Equiv _ _
      unfold ComoduleExtension.Equiv ComoduleExtension.ofSkewPrimitive
      simp only
      have hab' : a - b ∈ Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
          (trivialSkewPrimitiveSubspace (k := k) g h) := by
        exact (Submodule.quotientRel_def _).mp hab
      rw [Submodule.mem_comap] at hab'
      simp only [Submodule.subtype_apply, Submodule.coe_sub] at hab'
      exact hab')

/-- The canonical bijection between `Ext¹(k·h, k·g)` and the reduced skew-primitive quotient
`skewPrimitiveSpace g h / trivialSkewPrimitiveSubspace g h`. -/
def ext1EquivSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h ≃ SkewQuot (k := k) g h where
  toFun := ext1ToSkewQuot
  invFun := skewQuotToExt1
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h E =>
      simp only [ext1ToSkewQuot, skewQuotToExt1, ComoduleExt1.mk,
        ComoduleExtension.ofSkewPrimitive]
      rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h p =>
      simp only [ext1ToSkewQuot, skewQuotToExt1, ComoduleExt1.mk,
        ComoduleExtension.ofSkewPrimitive]
      rfl

/-- Additive group structure on `ComoduleExt1` transported from the reduced skew-primitive
quotient. -/
noncomputable instance ComoduleExt1.instAddCommGroup {g h : C} :
    AddCommGroup (ComoduleExt1 (k := k) g h) :=
  (ext1EquivSkewQuot (k := k)).addCommGroup

/-- `k`-module structure on `ComoduleExt1` transported from the reduced skew-primitive quotient. -/
noncomputable instance ComoduleExt1.instModule {g h : C} :
    Module k (ComoduleExt1 (k := k) g h) :=
  Equiv.module k (ext1EquivSkewQuot (k := k))

end Proposition_1_27_1_proof

/-- Corollary 1.27.6: in characteristic zero, a finite-dimensional bialgebra has no nonzero
primitive elements. -/
def residueFieldEquivOfAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type u) [CommRing H] [Algebra k H] [Module.Finite k H]
    (I : MaximalSpectrum H) : k ≃ₐ[k] (H ⧸ I.asIdeal) := by
  haveI : IsDomain (H ⧸ I.asIdeal) := Ideal.Quotient.isDomain I.asIdeal
  haveI : Module.Finite k (H ⧸ I.asIdeal) := Module.Finite.quotient k I.asIdeal
  haveI : Algebra.IsIntegral k (H ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ I.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- If a finite-dimensional commutative Hopf algebra `H` is isomorphic to the function algebras
`k^G₁` and `k^G₂` for two finite groups, then those groups are canonically isomorphic. -/
section Helpers

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
