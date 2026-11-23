module

public import Theorem.Scheme.OrderedAffineCoverCech

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)


public theorem frontFace_apply (a b n : ℕ) (h : a + b = n) (s : K.Idx n) (j : Fin (a + 1)) :
    (K.frontFace a b n h s).1 j = s.1 ⟨j.1, by omega⟩ :=
  rfl


public theorem backFace_apply (a b n : ℕ) (h : a + b = n) (s : K.Idx n) (j : Fin (b + 1)) :
    (K.backFace a b n h s).1 j = s.1 ⟨a + j.1, by omega⟩ :=
  rfl


public theorem inter_le_inter_frontFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    K.inter s ≤ K.inter (K.frontFace a b n h s) :=
  le_iInf fun _ => iInf_le _ _


public theorem inter_le_inter_backFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    K.inter s ≤ K.inter (K.backFace a b n h s) :=
  le_iInf fun _ => iInf_le _ _

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)


public theorem cup_apply (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b) (s : K.Idx n) :
    F.cup K a b n h α β s =
      (V.presheaf.map (homOfLE (K.inter_le_inter_frontFace a b n h s)).op).hom (α (K.frontFace a b n h s))
        • F.res (K.inter_le_inter_backFace a b n h s) (β (K.backFace a b n h s)) :=
  rfl

end OModulePresheaf

end AlgebraicGeometry

end
