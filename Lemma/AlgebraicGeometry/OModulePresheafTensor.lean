import Lemma.AlgebraicGeometry.OModulePresheafOfModules
import Mathlib.LinearAlgebra.TensorProduct.Basic

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F G : OModulePresheaf π)

@[reducible] def tensorObjModule (U : V.Opens) : Module R (F.obj U ⊗[Γ(V, U)] G.obj U) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  Module.compHom (F.obj U ⊗[Γ(V, U)] G.obj U) (algebraMap R Γ(V, U))

def tensorResₛₗ {U U' : V.Opens} (h : U ≤ U') :
    F.obj U' ⊗[Γ(V, U')] G.obj U' →ₛₗ[(V.presheaf.map (homOfLE h).op).hom] F.obj U ⊗[Γ(V, U)] G.obj U :=
  TensorProduct.lift
    (LinearMap.mk₂'ₛₗ (V.presheaf.map (homOfLE h).op).hom (V.presheaf.map (homOfLE h).op).hom
      (fun x y => F.res h x ⊗ₜ[Γ(V, U)] G.res h y)
      (fun x₁ x₂ y => by simp only [map_add, add_tmul])
      (fun a x y => by simp only [F.res_smul, smul_tmul'])
      (fun x y₁ y₂ => by simp only [map_add, tmul_add])
      (fun a x y => by simp only [G.res_smul, tmul_smul]))

theorem tensorResₛₗ_tmul {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') (y : G.obj U') :
    F.tensorResₛₗ G h (x ⊗ₜ y) = F.res h x ⊗ₜ G.res h y := rfl

def tensorRes {U U' : V.Opens} (h : U ≤ U') :
    letI := F.tensorObjModule G U; letI := F.tensorObjModule G U'
    F.obj U' ⊗[Γ(V, U')] G.obj U' →ₗ[R] F.obj U ⊗[Γ(V, U)] G.obj U :=
  letI := F.tensorObjModule G U; letI := F.tensorObjModule G U'
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U'
  { toFun := F.tensorResₛₗ G h
    map_add' := fun s t => map_add _ s t
    map_smul' := fun r t => by
      show F.tensorResₛₗ G h (algebraMap R Γ(V, U') r • t) = algebraMap R Γ(V, U) r • F.tensorResₛₗ G h t
      rw [LinearMap.map_smulₛₗ]
      congr 1
      exact (Scheme.TwoAffineOpenCover.restrictAlgHom π h).commutes r }

def tensor : OModulePresheaf π where
  obj U := F.obj U ⊗[Γ(V, U)] G.obj U
  addCommGroup _ := inferInstance
  module U := F.tensorObjModule G U
  moduleSections _ := inferInstance
  isScalarTower U :=

    @IsScalarTower.mk R Γ(V, U) _ (_) (_) (_)
      fun r a t => mul_smul ((Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r) a t
  res h := F.tensorRes G h
  res_smul h a t := (F.tensorResₛₗ G h).map_smulₛₗ a t
  res_refl U := by
    letI := F.tensorObjModule G U
    refine LinearMap.ext fun t => ?_
    show F.tensorResₛₗ G (le_refl U) t = t
    induction t using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul x y => rw [tensorResₛₗ_tmul, res_refl_apply, res_refl_apply]
    | add s t hs ht => rw [map_add, hs, ht]
  res_comp {U U' U''} h h' := by
    letI := F.tensorObjModule G U; letI := F.tensorObjModule G U''
    refine LinearMap.ext fun t => ?_
    show F.tensorResₛₗ G (h.trans h') t = F.tensorResₛₗ G h (F.tensorResₛₗ G h' t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rw [tensorResₛₗ_tmul, tensorResₛₗ_tmul, tensorResₛₗ_tmul, res_res, res_res]
    | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]

theorem tensor_obj (U : V.Opens) : (F.tensor G).obj U = (F.obj U ⊗[Γ(V, U)] G.obj U) := rfl

theorem tensor_res_tmul {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') (y : G.obj U') :
    (F.tensor G).res h (show (F.tensor G).obj U' from x ⊗ₜ y)
      = (show (F.tensor G).obj U from F.res h x ⊗ₜ G.res h y) := rfl

theorem tensor_res_apply {U U' : V.Opens} (h : U ≤ U') (t : F.obj U' ⊗[Γ(V, U')] G.obj U') :
    (F.tensor G).res h (show (F.tensor G).obj U' from t) = (show (F.tensor G).obj U from F.tensorResₛₗ G h t) :=
  rfl

theorem tensor_smul_tmul (U : V.Opens) (a : Γ(V, U)) (x : F.obj U) (y : G.obj U) :
    a • (show (F.tensor G).obj U from x ⊗ₜ y) = (show (F.tensor G).obj U from (a • x) ⊗ₜ y) := rfl

theorem tensor_algebraMap_smul (U : V.Opens) (r : R) (t : (F.tensor G).obj U) :
    r • t = (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r • t := rfl

section Twist

variable (L : V.Modules)

abbrev twist : OModulePresheaf π := F.tensor (ofModules π L)

theorem twist_obj (U : V.Opens) : (F.twist L).obj U = (F.obj U ⊗[Γ(V, U)] Γ(L, U)) := rfl

theorem twist_res_tmul {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') (y : Γ(L, U')) :
    (F.twist L).res h (show (F.twist L).obj U' from x ⊗ₜ[Γ(V, U')] (show (ofModules π L).obj U' from y))
      = (show (F.twist L).obj U from
          F.res h x ⊗ₜ[Γ(V, U)] (show (ofModules π L).obj U from L.presheaf.map (homOfLE h).op y)) :=
  rfl

end Twist

end AlgebraicGeometry.OModulePresheaf

end
