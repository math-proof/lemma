import Mathlib

import Def.AlgebraicGeometry_OModulePresheafHom
import Instance.AlgebraicGeometry_OrderedAffineCoverOf
import Structure.AlgebraicGeometry_OrderedAffineCoverOf

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {V : Scheme.{u}}


namespace Scheme.OrderedAffineCoverOf

variable {W : V.Opens} (K : V.OrderedAffineCoverOf W)

def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j

theorem inter_le_base {i : ℕ} (s : K.Idx i) : K.inter s ≤ W := (iInf_le _ 0).trans (K.le _)

end Scheme.OrderedAffineCoverOf

namespace Scheme.OrderedAffineCover

def toCoverOf (K : V.OrderedAffineCover) : V.OrderedAffineCoverOf ⊤ where
  ι := K.ι
  U := K.U
  isAffineOpen := K.isAffineOpen
  le _ := le_top
  iSup_eq := K.iSup_eq_top

@[simp] theorem toCoverOf_U (K : V.OrderedAffineCover) (i : K.ι) : K.toCoverOf.U i = K.U i := rfl

def restrict (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) : V.OrderedAffineCoverOf W where
  ι := K.ι
  U i := K.U i ⊓ W
  isAffineOpen i := isAffineOpen_inf_of_isSeparated π (K.isAffineOpen i) hW
  le _ := inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K.iSup_eq_top, top_inf_eq]

@[simp] theorem restrict_U (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) (i : K.ι) : (K.restrict π hW).U i = K.U i ⊓ W := rfl

end Scheme.OrderedAffineCover

namespace Scheme.OrderedAffineCoverOf

variable (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W)

@[reducible] def moduleSections : ∀ O : V.Opens, Module R Γ(V, O) :=
  fun O => (Scheme.TwoAffineOpenCover.algebraOfHom π O).toModule

abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, Γ(V, K.inter s)

def res {O O' : V.Opens} (h : O ≤ O') :
    letI := moduleSections π
    (Γ(V, O') : Type u) →ₗ[R] (Γ(V, O) : Type u) :=
  (OModulePresheaf.unit π).res h

theorem res_apply {O O' : V.Opens} (h : O ≤ O') (x : Γ(V, O')) :
    res π h x = (V.presheaf.map (homOfLE h).op).hom x := rfl

def d (i : ℕ) :
    letI := moduleSections π
    K.cochain i →ₗ[R] K.cochain (i + 1) :=
  letI := moduleSections π
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((res π (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (f : K.cochain i) (s : K.Idx (i + 1)) :
    letI := moduleSections π
    K.d π i f s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (V.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (f (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, res_apply]

def aug :
    letI := moduleSections π
    (Γ(V, W) : Type u) →ₗ[R] K.cochain 0 :=
  letI := moduleSections π
  LinearMap.pi fun s => res π (K.inter_le_base s)

theorem aug_apply (w : Γ(V, W)) (s : K.Idx 0) :
    letI := moduleSections π
    K.aug π w s = (V.presheaf.map (homOfLE (K.inter_le_base s)).op).hom w := rfl

abbrev H0 : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π 0)

abbrev HSucc (i : ℕ) : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π (i + 1)) ⧸ (LinearMap.range (K.d π i)).comap (LinearMap.ker (K.d π (i + 1))).subtype

end Scheme.OrderedAffineCoverOf

theorem Scheme.OrderedAffineCover.d_toCoverOf (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover) (i : ℕ) :
    K.toCoverOf.d π i = (OModulePresheaf.unit π).d K i := rfl

end AlgebraicGeometry

end
