module

public import Mathlib
public import Def.AlgebraicGeometry_OrderedAffineCoverCech
public import Def.AlgebraicGeometry_DoubleComplex
public import Instance.AlgebraicGeometry_BiCech
public import Structure.AlgebraicGeometry_BiCech

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Scheme

namespace AlgebraicGeometry


namespace Scheme.OrderedOpenFamily

variable {Z : Scheme.{u}} (𝔄 : Z.OrderedOpenFamily)

def Idx (p : ℕ) : Type u := {s : Fin (p + 1) → 𝔄.ι // StrictMono s}

def inter {p : ℕ} (s : 𝔄.Idx p) : Z.Opens := ⨅ j, 𝔄.U (s.1 j)

def face {p : ℕ} (s : 𝔄.Idx (p + 1)) (j : Fin (p + 2)) : 𝔄.Idx p :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

def prodCover (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) : Z.OrderedAffineCover where
  ι := 𝔄.ι ×ₗ 𝔅.ι
  instFintype := inferInstanceAs (Fintype (𝔄.ι × 𝔅.ι))
  instLinearOrder := inferInstance
  U ij := 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2
  isAffineOpen ij := haff _ _
  iSup_eq_top := by
    rw [← hcov]
    exact le_antisymm (iSup_le fun ij => le_iSup (fun ij : 𝔄.ι × 𝔅.ι => 𝔄.U ij.1 ⊓ 𝔅.U ij.2) (ofLex ij))
      (iSup_le fun ij => le_iSup (fun ij : 𝔄.ι ×ₗ 𝔅.ι => 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2) (toLex ij))

end Scheme.OrderedOpenFamily

namespace Scheme.OrderedAffineCover

def toOpenFamily {Z : Scheme.{u}} (K : Z.OrderedAffineCover) : Z.OrderedOpenFamily where
  ι := K.ι
  U := K.U

def imageFamily {W Z : Scheme.{u}} (K : W.OrderedAffineCover) (f : W ⟶ Z) [IsOpenImmersion f] :
    Z.OrderedOpenFamily where
  ι := K.ι
  U i := f ''ᵁ K.U i

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
variable (𝔄 𝔅 : Z.OrderedOpenFamily)

namespace BiCech

abbrev C (p q : ℕ) : Type u := ∀ st : 𝔄.Idx p × 𝔅.Idx q, F.obj (𝔄.inter st.1 ⊓ 𝔅.inter st.2)

def dH (p q : ℕ) : C F 𝔄 𝔅 p q →ₗ[R] C F 𝔄 𝔅 (p + 1) q :=
  LinearMap.pi fun st => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (inter_inf_le_left 𝔄 𝔅 st.1 st.2 j)).comp (LinearMap.proj (𝔄.face st.1 j, st.2)))

def dV (p q : ℕ) : C F 𝔄 𝔅 p q →ₗ[R] C F 𝔄 𝔅 p (q + 1) :=
  LinearMap.pi fun st => ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (inter_inf_le_right 𝔄 𝔅 st.1 st.2 j)).comp (LinearMap.proj (st.1, 𝔅.face st.2 j)))

end BiCech

@[reducible] def biCech : DoubleComplex.Bounded R where
  C := BiCech.C F 𝔄 𝔅
  dH := BiCech.dH F 𝔄 𝔅
  dV := BiCech.dV F 𝔄 𝔅
  dH_sq := BiCech.dH_sq F 𝔄 𝔅
  dV_sq := BiCech.dV_sq F 𝔄 𝔅
  dHV_comm := BiCech.dHV_comm F 𝔄 𝔅
  N := max (Fintype.card 𝔄.ι) (Fintype.card 𝔅.ι)
  hBound p q h := by
    rcases h with h | h
    · haveI := 𝔄.isEmpty_idx_of_card_le ((le_max_left _ _).trans h)
      infer_instance
    · haveI := 𝔅.isEmpty_idx_of_card_le ((le_max_right _ _).trans h)
      infer_instance

end OModulePresheaf

end AlgebraicGeometry

end

end
