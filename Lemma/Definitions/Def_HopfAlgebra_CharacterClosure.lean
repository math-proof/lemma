import Mathlib
import Lemma.Definitions.Def_HopfAlgebra_CartierDual
import Lemma.Definitions.Def_FiniteFlat_SchematicClosure

set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra

section FieldLevel

variable {F : Type*} [CommRing F] {A : Type*} [CommRing A] [Algebra F A]
variable {L : Type*} [CommRing L] [Algebra F L]

def vanishingIdealOfPoints (S : Set (A →ₐ[F] L)) : Ideal A where
  carrier := {a | ∀ ν ∈ S, ν a = 0}
  add_mem' {a b} ha hb := fun ν hν => by rw [map_add, ha ν hν, hb ν hν, add_zero]
  zero_mem' := fun ν _ => map_zero ν
  smul_mem' c {a} ha := fun ν hν => by rw [smul_eq_mul, map_mul, ha ν hν, mul_zero]

@[simp] theorem mem_vanishingIdealOfPoints_iff (S : Set (A →ₐ[F] L)) (a : A) :
    a ∈ vanishingIdealOfPoints S ↔ ∀ ν ∈ S, ν a = 0 := Iff.rfl

theorem vanishingIdealOfPoints_antitone {S T : Set (A →ₐ[F] L)} (h : S ⊆ T) :
    vanishingIdealOfPoints T ≤ vanishingIdealOfPoints S := fun _ ha ν hν => ha ν (h hν)

def liftPoint (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) :
    (A ⧸ vanishingIdealOfPoints S) →ₐ[F] L :=
  Ideal.Quotient.liftₐ (vanishingIdealOfPoints S) ν (fun a ha => ha ν hν)

@[simp] theorem liftPoint_mk (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) (a : A) :
    liftPoint S ν hν (Ideal.Quotient.mk (vanishingIdealOfPoints S) a) = ν a := rfl

noncomputable def evalPair (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) :
    (A ⧸ vanishingIdealOfPoints S) ⊗[F] (A ⧸ vanishingIdealOfPoints S) →ₐ[F] L :=
  (Algebra.TensorProduct.lmul' F (S := L)).comp
    (Algebra.TensorProduct.map (liftPoint S ν hν) (liftPoint S ν' hν'))

theorem evalPair_tmul (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) (a b : A) :
    evalPair S ν ν' hν hν' (Ideal.Quotient.mk _ a ⊗ₜ[F] Ideal.Quotient.mk _ b) = ν a * ν' b := by
  simp only [evalPair, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul, liftPoint_mk,
    Algebra.TensorProduct.lmul'_apply_tmul]

end FieldLevel

section PointMonoid

variable {F : Type*} [CommRing F] {A : Type*} [CommRing A] [Bialgebra F A]
variable {L : Type*} [CommRing L] [Algebra F L]

def ptSet (S : Submonoid (WithConv (A →ₐ[F] L))) : Set (A →ₐ[F] L) := {ν | WithConv.toConv ν ∈ S}

@[simp] theorem mem_ptSet_iff (S : Submonoid (WithConv (A →ₐ[F] L))) (ν : A →ₐ[F] L) :
    ν ∈ ptSet S ↔ WithConv.toConv ν ∈ S := Iff.rfl

theorem ofConv_mem_ptSet {S : Submonoid (WithConv (A →ₐ[F] L))} (ν : ↥S) : WithConv.ofConv ν.1 ∈ ptSet S := by
  show WithConv.toConv (WithConv.ofConv ν.1) ∈ S
  exact ν.2

theorem ptSet_mono {S T : Submonoid (WithConv (A →ₐ[F] L))} (h : S ≤ T) : ptSet S ⊆ ptSet T :=
  fun _ hν => h hν

abbrev pointQuot (S : Submonoid (WithConv (A →ₐ[F] L))) : Type _ := A ⧸ vanishingIdealOfPoints (ptSet S)

noncomputable def evalQuot (S : Submonoid (WithConv (A →ₐ[F] L))) : L ⊗[F] pointQuot S →ₐ[L] (↥S → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (Pi.algHom F _ fun ν => liftPoint (ptSet S) (WithConv.ofConv ν.1) (ofConv_mem_ptSet ν))
    (fun _ _ => Commute.all _ _)

theorem evalQuot_tmul (S : Submonoid (WithConv (A →ₐ[F] L))) (c : L) (a : A) (ν : ↥S) :
    evalQuot S (c ⊗ₜ[F] Ideal.Quotient.mk _ a) ν = c * (WithConv.ofConv ν.1) a := by
  simp only [evalQuot, Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply]
  rw [Algebra.ofId_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

end PointMonoid

end HopfAlgebra

namespace CartierDual

section BaseChange

universe u v w

variable (O : Type u) [CommRing O] (F : Type v) [CommRing F] [Algebra O F]
variable (A : Type w) [CommRing A] [Bialgebra O A]

theorem add_apply_pt {R : Type*} [CommRing R] {X : Type*} [CommRing X] [Bialgebra R X]
    (φ ψ : CartierDual R X) (x : X) : (φ + ψ) x = φ x + ψ x := by
  rw [← CartierDual.toDual_apply (φ + ψ), map_add, LinearMap.add_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply]

theorem zero_apply_pt {R : Type*} [CommRing R] {X : Type*} [CommRing X] [Bialgebra R X]
    (x : X) : (0 : CartierDual R X) x = 0 := by
  rw [← CartierDual.toDual_apply (0 : CartierDual R X), map_zero, LinearMap.zero_apply]

theorem smul_apply_pt {R : Type*} [CommRing R] {X : Type*} [CommRing X] [Bialgebra R X]
    (c : R) (φ : CartierDual R X) (x : X) : (c • φ) x = c * φ x := by
  rw [← CartierDual.toDual_apply (c • φ), LinearEquiv.map_smul, LinearMap.smul_apply, smul_eq_mul,
    CartierDual.toDual_apply]

noncomputable instance instModuleRestrictBaseChange : Module O (CartierDual F (F ⊗[O] A)) :=
  Module.compHom (CartierDual F (F ⊗[O] A)) (algebraMap O F)

instance instIsScalarTowerRestrictBaseChange : IsScalarTower O F (CartierDual F (F ⊗[O] A)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable instance instRingBaseChangeDual : Ring (F ⊗[O] CartierDual O A) := Algebra.TensorProduct.instRing

noncomputable instance instAlgebraBaseChangeDual : Algebra F (F ⊗[O] CartierDual O A) :=
  Algebra.TensorProduct.leftAlgebra

variable {O F A}

noncomputable def dualBaseChange (φ : CartierDual O A) : CartierDual F (F ⊗[O] A) :=
  CartierDual.ofDual F (F ⊗[O] A)
    ((TensorProduct.AlgebraTensorModule.rid O F F).toLinearMap ∘ₗ LinearMap.baseChange F (CartierDual.toDual O A φ))

@[simp] theorem dualBaseChange_tmul (φ : CartierDual O A) (c : F) (a : A) :
    dualBaseChange (F := F) φ (c ⊗ₜ[O] a) = c * algebraMap O F (φ a) := by
  show (TensorProduct.AlgebraTensorModule.rid O F F) ((LinearMap.baseChange F (CartierDual.toDual O A φ)) (c ⊗ₜ[O] a)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul, CartierDual.toDual_apply, Algebra.smul_def,
    mul_comm]

variable (O F A) in

noncomputable def dualBaseChangeHom : CartierDual O A →ₗ[O] CartierDual F (F ⊗[O] A) where
  toFun := dualBaseChange
  map_add' φ ψ := by
    refine CartierDual.ext fun x => ?_
    rw [add_apply_pt]
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, add_zero]
    | tmul c a =>
      rw [dualBaseChange_tmul, dualBaseChange_tmul, dualBaseChange_tmul, add_apply_pt, map_add, mul_add]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel
  map_smul' r φ := by
    refine CartierDual.ext fun x => ?_
    rw [RingHom.id_apply]
    show dualBaseChange (r • φ) x = ((algebraMap O F r) • dualBaseChange φ) x
    rw [smul_apply_pt]
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, mul_zero]
    | tmul c a => rw [dualBaseChange_tmul, dualBaseChange_tmul, smul_apply_pt, map_mul]; ring
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

variable (O F A) in

noncomputable def dualBaseChangeLin : F ⊗[O] CartierDual O A →ₗ[F] CartierDual F (F ⊗[O] A) :=
  LinearMap.liftBaseChange F (dualBaseChangeHom O F A)

@[simp] theorem dualBaseChangeLin_tmul (c : F) (φ : CartierDual O A) :
    dualBaseChangeLin O F A (c ⊗ₜ[O] φ) = c • dualBaseChange φ :=
  LinearMap.liftBaseChange_tmul F _ c φ

theorem dualBaseChangeLin_tmul_tmul (c : F) (φ : CartierDual O A) (c' : F) (a : A) :
    dualBaseChangeLin O F A (c ⊗ₜ[O] φ) (c' ⊗ₜ[O] a) = c * c' * algebraMap O F (φ a) := by
  rw [dualBaseChangeLin_tmul, smul_apply_pt, dualBaseChange_tmul, mul_assoc]

end BaseChange

end CartierDual

namespace HopfAlgebra

section Character

universe u v w

variable (O : Type u) [CommRing O] (F : Type v) [CommRing F] [Algebra O F]
variable (A : Type w) [CommRing A] [Bialgebra O A]
variable (L : Type*) [CommRing L] [Algebra F L]

noncomputable def characterGenericFibre (S : Set (F ⊗[O] A →ₐ[F] L)) : Subalgebra F (F ⊗[O] CartierDual O A) :=
  Algebra.adjoin F {w | ∀ x ∈ vanishingIdealOfPoints S, CartierDual.dualBaseChangeLin O F A w x = 0}

theorem characterGenericFibre_mono {S T : Set (F ⊗[O] A →ₐ[F] L)} (h : S ⊆ T) :
    characterGenericFibre O F A L S ≤ characterGenericFibre O F A L T := by
  apply Algebra.adjoin_mono
  intro w hw x hx
  exact hw x (vanishingIdealOfPoints_antitone h hx)

theorem subset_characterGenericFibre (S : Set (F ⊗[O] A →ₐ[F] L)) :
    {w | ∀ x ∈ vanishingIdealOfPoints S, CartierDual.dualBaseChangeLin O F A w x = 0}
      ⊆ (characterGenericFibre O F A L S : Set (F ⊗[O] CartierDual O A)) :=
  Algebra.subset_adjoin

end Character

section Closure

universe u v w

variable (O : Type u) [CommRing O] (F : Type v) [Field F] [Algebra O F]
variable (A : Type w) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
variable (L : Type*) [CommRing L] [Algebra F L]

noncomputable abbrev characterClosure (S : Set (F ⊗[O] A →ₐ[F] L)) : Subalgebra O (CartierDual O A) :=
  flatClosure (characterGenericFibre O F A L S)

theorem mem_characterClosure_iff (S : Set (F ⊗[O] A →ₐ[F] L)) (g : CartierDual O A) :
    g ∈ characterClosure O F A L S ↔ (1 : F) ⊗ₜ[O] g ∈ characterGenericFibre O F A L S := Iff.rfl

theorem characterClosure_mono {S T : Set (F ⊗[O] A →ₐ[F] L)} (h : S ⊆ T) :
    characterClosure O F A L S ≤ characterClosure O F A L T :=
  flatClosure_mono (characterGenericFibre_mono O F A L h)

end Closure

end HopfAlgebra
