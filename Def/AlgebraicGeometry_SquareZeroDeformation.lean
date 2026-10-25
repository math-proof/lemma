import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Instance.AlgebraicGeometry_SquareZeroDeformation
import Abbrev.AlgebraicGeometry_SquareZeroDeformation

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TrivSqZeroExt NeronModelInfra

namespace AlgebraicGeometry

namespace SquareZero

variable (K : Type u) [Field K]
variable (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

def toBase : spec K V ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K V)))

def basePoint : Spec (CommRingCat.of K) ⟶ spec K V :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom)

@[reassoc (attr := simp)]
theorem basePoint_toBase : basePoint K V ≫ toBase K V = 𝟙 _ := by
  rw [basePoint, toBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1

def basePointOver : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase K V) :=
  ⟨basePoint K V, basePoint_toBase K V⟩

@[simp] theorem basePointOver_coe : (basePointOver K V).1 = basePoint K V := rfl

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
variable {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W']

def specMap (φ : V →ₗ[K] W) : spec K W ⟶ spec K V :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map φ).toRingHom)

@[reassoc (attr := simp)]
theorem specMap_toBase (φ : V →ₗ[K] W) : specMap K φ ≫ toBase K V = toBase K W := by
  rw [specMap, toBase, toBase, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change TrivSqZeroExt.map φ (algebraMap K _ a) = algebraMap K _ a
  exact (TrivSqZeroExt.map φ).commutes a

@[reassoc (attr := simp)]
theorem basePoint_specMap (φ : V →ₗ[K] W) : basePoint K W ≫ specMap K φ = basePoint K V := by
  rw [specMap, basePoint, basePoint, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (TrivSqZeroExt.map φ a).fst = a.fst
  exact TrivSqZeroExt.fst_map φ a

theorem specMap_id : specMap K (LinearMap.id : V →ₗ[K] V) = 𝟙 _ := by
  rw [specMap, TrivSqZeroExt.map_id, ← Spec.map_id]
  rfl

theorem specMap_comp (φ : V →ₗ[K] W) (ψ : W →ₗ[K] W') :
    specMap K (ψ ∘ₗ φ) = specMap K ψ ≫ specMap K φ := by
  rw [specMap, specMap, specMap, ← Spec.map_comp, TrivSqZeroExt.map_comp_map]
  rfl

def specMapOver (φ : V →ₗ[K] W) : SchemeHomOver (toBase K W) (toBase K V) :=
  ⟨specMap K φ, specMap_toBase K φ⟩

@[simp] theorem specMapOver_coe (φ : V →ₗ[K] W) : (specMapOver K φ).1 = specMap K φ := rfl

end SquareZero

section TangentPoints

variable {K : Type u} [Field K] {X : Scheme.{u}}

def TangentPoints (x : X ⟶ Spec (CommRingCat.of K)) (pt : Spec (CommRingCat.of K) ⟶ X)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] : Type u :=
  { v : SquareZero.spec K V ⟶ X // v ≫ x = SquareZero.toBase K V ∧ SquareZero.basePoint K V ≫ v = pt }

namespace TangentPoints

variable {x : X ⟶ Spec (CommRingCat.of K)} {pt : Spec (CommRingCat.of K) ⟶ X}
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

@[ext] theorem ext {v v' : TangentPoints x pt V} (h : v.1 = v'.1) : v = v' := Subtype.ext h

def map (φ : V →ₗ[K] W) (v : TangentPoints x pt V) : TangentPoints x pt W :=
  ⟨SquareZero.specMap K φ ≫ v.1, by rw [Category.assoc, v.2.1, SquareZero.specMap_toBase],
    by rw [SquareZero.basePoint_specMap_assoc, v.2.2]⟩

@[simp] theorem map_coe (φ : V →ₗ[K] W) (v : TangentPoints x pt V) :
    (v.map φ).1 = SquareZero.specMap K φ ≫ v.1 := rfl


end TangentPoints

namespace RelPicard

variable {K : Type u} [Field K] {C : Scheme.{u}}

def TrivialModDeformations (c : C ⟶ Spec (CommRingCat.of K))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] : Type (u + 1) :=
  { L : RigidifiedLineBundle c ε (SquareZero.toBase K V) //
      Nonempty ((L.pullbackAlong (SquareZero.basePointOver K V)).L ≅
        (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 (Spec (CommRingCat.of K)))).L) }

namespace TrivialModDeformations

variable {c : C ⟶ Spec (CommRingCat.of K)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem postComp_specMapOver_basePointOver (φ : V →ₗ[K] W) :
    postComp (SquareZero.specMapOver K φ) (SquareZero.basePointOver K W) = SquareZero.basePointOver K V :=
  Subtype.ext (SquareZero.basePoint_specMap K φ)

def map (φ : V →ₗ[K] W) (L : TrivialModDeformations c ε V) : TrivialModDeformations c ε W :=
  ⟨L.1.pullbackAlong (SquareZero.specMapOver K φ),
    ⟨(Scheme.Modules.pullbackComp _ _).app L.1.L ≪≫
      (Scheme.Modules.pullbackCongr
        ((baseChangeSnd_comp c (SquareZero.specMapOver K φ) (SquareZero.basePointOver K W)).trans
          (by rw [postComp_specMapOver_basePointOver]))).app L.1.L ≪≫
      L.2.some⟩⟩

@[simp] theorem map_coe (φ : V →ₗ[K] W) (L : TrivialModDeformations c ε V) :
    (L.map φ).1 = L.1.pullbackAlong (SquareZero.specMapOver K φ) := rfl

end TrivialModDeformations

end RelPicard

end AlgebraicGeometry

end
