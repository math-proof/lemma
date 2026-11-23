module

public import Def.AlgebraicGeometry_OrderedAffineCoverCech

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

def frontFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) : K.Idx a :=
  ⟨fun j => s.1 ⟨j.1, by omega⟩, fun _ _ hj => s.2 (Fin.mk_lt_mk.2 (Fin.lt_def.1 hj))⟩

def backFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) : K.Idx b :=
  ⟨fun j => s.1 ⟨a + j.1, by omega⟩, fun _ _ hj => s.2 (Fin.mk_lt_mk.2 (by have := Fin.lt_def.1 hj; omega))⟩

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def cup (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b) : F.cochain K n :=
  fun s => (V.presheaf.map (homOfLE (K.inter_le_inter_frontFace a b n h s)).op).hom (α (K.frontFace a b n h s))
    • F.res (K.inter_le_inter_backFace a b n h s) (β (K.backFace a b n h s))

end OModulePresheaf

end AlgebraicGeometry

end

end
