import Mathlib
import Def.AlgebraicGeometry_OrderedAffineCoverCech
import Lemma.Scheme.OrderedAffineCoverComap

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)

def sortIdx {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) : 𝒦.Idx n :=
  ⟨(lam ∘ s.1) ∘ (Tuple.sort (lam ∘ s.1)),
    (Tuple.monotone_sort (lam ∘ s.1)).strictMono_of_injective (hinj.comp (Tuple.sort (lam ∘ s.1)).injective)⟩

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}

def unitPullback (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) : (unit πX).cochain 𝒲 n :=
  fun s => by
end AlgebraicGeometry.OModulePresheaf

end
