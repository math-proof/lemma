import Def.AlgebraicGeometry_OrderedAffineCoverCech
import Def.AlgebraicGeometry_OrderedAffineCoverCechCup
import Def.AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

abbrev OIdx (n : ℕ) : Type u := Fin (n + 1) → K.ι

def ointer {n : ℕ} (t : K.OIdx n) : V.Opens := ⨅ j, K.U (t j)

def oface {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) : K.OIdx n := t ∘ Fin.succAbove j

def ofrontFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) : K.OIdx a := fun j => t ⟨j.1, by omega⟩

def obackFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) : K.OIdx b := fun j => t ⟨a + j.1, by omega⟩

def osort {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) : K.Idx n :=
  ⟨t ∘ Tuple.sort t, (Tuple.monotone_sort t).strictMono_of_injective (hinj.comp (Tuple.sort t).injective)⟩

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

abbrev ocochain (n : ℕ) : Type u := ∀ t : K.OIdx n, F.obj (K.ointer t)

def od (n : ℕ) : F.ocochain K n →ₗ[R] F.ocochain K (n + 1) :=
  haveI := Classical.decEq (K.OIdx n)
  LinearMap.pi fun t => ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (K.ointer_le_ointer_oface t j)).comp (LinearMap.proj (K.oface t j)))

def ocup (a b n : ℕ) (h : a + b = n) (α : (unit π).ocochain K a) (β : F.ocochain K b) : F.ocochain K n :=
  fun t => (V.presheaf.map (homOfLE (K.ointer_le_ointer_ofrontFace a b n h t)).op).hom (α (K.ofrontFace a b n h t))
    • F.res (K.ointer_le_ointer_obackFace a b n h t) (β (K.obackFace a b n h t))

def ores (n : ℕ) : F.ocochain K n →ₗ[R] F.cochain K n :=
  haveI := Classical.decEq (K.OIdx n)
  LinearMap.pi fun s => LinearMap.proj (R := R) (φ := fun t : K.OIdx n => F.obj (K.ointer t)) s.1

def oext (n : ℕ) : F.cochain K n →ₗ[R] F.ocochain K n :=
  haveI := Classical.decEq (K.OIdx n)
  haveI := K.decidableEq_Idx n
  LinearMap.pi fun t => by
variable {R' : Type u} [CommRing R'] {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}

def ounitPullback (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (c : (unit πY).ocochain 𝒦 n) : (unit πX).ocochain 𝒲 n :=
  fun t => (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).op).hom
    ((h.app (𝒦.ointer (lam ∘ t))).hom (c (lam ∘ t)))

end OModulePresheaf

end AlgebraicGeometry

end
