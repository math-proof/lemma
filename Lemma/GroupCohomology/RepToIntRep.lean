import Mathlib

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type} [CommRing k] [Group G]

def toIntRepρ (M : Rep k G) : Representation ℤ G M.V where
  toFun g := (M.ρ g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by simp

@[simp] lemma toIntRepρ_apply_apply (M : Rep k G) (g : G) (x : M.V) : M.toIntRepρ g x = M.ρ g x := rfl

def toIntRep (M : Rep k G) : Rep ℤ G := Rep.of M.toIntRepρ

lemma coe_toIntRep (M : Rep k G) : (M.toIntRep : Type) = M.V := rfl

@[simp] lemma toIntRep_ρ (M : Rep k G) : M.toIntRep.ρ = M.toIntRepρ := rfl

lemma toIntRep_ρ_apply_apply (M : Rep k G) (g : G) (x : M.V) : M.toIntRep.ρ g x = M.ρ g x := rfl

def toIntRepMap {M N : Rep k G} (φ : M ⟶ N) : M.toIntRep ⟶ N.toIntRep :=
  Rep.ofHom ⟨φ.hom.toAddMonoidHom.toIntLinearMap, fun g => LinearMap.ext fun x => Rep.hom_comm_apply φ g x⟩

@[simp] lemma toIntRepMap_hom_apply {M N : Rep k G} (φ : M ⟶ N) (x : M.V) : (toIntRepMap φ).hom x = φ.hom x := rfl

lemma toIntRepMap_id (M : Rep k G) : toIntRepMap (𝟙 M) = 𝟙 M.toIntRep := by ext x; rfl

lemma toIntRepMap_comp {M N P : Rep k G} (φ : M ⟶ N) (ψ : N ⟶ P) :
    toIntRepMap (φ ≫ ψ) = toIntRepMap φ ≫ toIntRepMap ψ := by ext x; rfl

variable (k G) in

def toIntRepFunctor : Rep k G ⥤ Rep ℤ G where
  obj M := M.toIntRep
  map φ := toIntRepMap φ
  map_id M := toIntRepMap_id M
  map_comp φ ψ := toIntRepMap_comp φ ψ

end Rep

end
