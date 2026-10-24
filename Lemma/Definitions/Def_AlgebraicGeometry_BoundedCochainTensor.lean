import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Lemma.Definitions.Def_AlgebraicGeometry_DoubleComplex
import Lemma.Definitions.Def_AlgebraicGeometry_BiCech

set_option autoImplicit false

noncomputable section

universe u

open TensorProduct AlgebraicGeometry

@[reducible] def AlgebraicGeometry.Scheme.OrderedAffineCover.preimageFamily {P Y : Scheme.{u}} (K : Y.OrderedAffineCover)
    (q : P ⟶ Y) : P.OrderedOpenFamily :=
  ⟨K.ι, fun i => q ⁻¹ᵁ K.U i⟩

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.preimageFamily_ι {P Y : Scheme.{u}} (K : Y.OrderedAffineCover)
    (q : P ⟶ Y) : (K.preimageFamily q).ι = K.ι := rfl

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.preimageFamily_U {P Y : Scheme.{u}} (K : Y.OrderedAffineCover)
    (q : P ⟶ Y) (i : K.ι) : (K.preimageFamily q).U i = q ⁻¹ᵁ K.U i := rfl

namespace CochainCx

structure Bounded (R : Type u) [CommRing R] where

  X : ℕ → Type u
  [abGrp : ∀ n, AddCommGroup (X n)]
  [modR : ∀ n, Module R (X n)]

  d : ∀ n, X n →ₗ[R] X (n + 1)
  d_sq : ∀ n, d (n + 1) ∘ₗ d n = 0

  N : ℕ
  hBound : ∀ n, N ≤ n → Subsingleton (X n)

attribute [instance] Bounded.abGrp Bounded.modR

namespace Bounded

variable {R : Type u} [CommRing R] (C D : Bounded R)

def B : (n : ℕ) → Submodule R (LinearMap.ker (C.d n))
  | 0 => ⊥
  | n + 1 => (LinearMap.range (C.d n)).comap (LinearMap.ker (C.d (n + 1))).subtype

abbrev H (n : ℕ) : Type u := LinearMap.ker (C.d n) ⧸ C.B n

abbrev hfinrank (n : ℕ) : ℕ := Module.finrank R (C.H n)

theorem B_zero : C.B 0 = ⊥ := rfl

theorem B_succ (n : ℕ) :
    C.B (n + 1) = (LinearMap.range (C.d n)).comap (LinearMap.ker (C.d (n + 1))).subtype := rfl

def tensor : DoubleComplex.Bounded R where
  C p q := C.X p ⊗[R] D.X q
  dH p q := (C.d p).rTensor (D.X q)
  dV p q := (D.d q).lTensor (C.X p)
  dH_sq p q := by
    rw [← LinearMap.rTensor_comp, C.d_sq, LinearMap.rTensor_zero]
  dV_sq p q := by
    rw [← LinearMap.lTensor_comp, D.d_sq, LinearMap.lTensor_zero]
  dHV_comm p q := by
    ext x y
    simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  N := max C.N D.N
  hBound p q h := by
    rcases h with h | h
    · haveI := C.hBound p (le_of_max_le_left h)
      infer_instance
    · haveI := D.hBound q (le_of_max_le_right h)
      infer_instance

theorem tensor_C (p q : ℕ) : (C.tensor D).C p q = (C.X p ⊗[R] D.X q) := rfl
theorem tensor_dH (p q : ℕ) : (C.tensor D).dH p q = (C.d p).rTensor (D.X q) := rfl
theorem tensor_dV (p q : ℕ) : (C.tensor D).dV p q = (D.d q).lTensor (C.X p) := rfl
theorem tensor_N : (C.tensor D).N = max C.N D.N := rfl

def ofCech {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) : Bounded R where
  X i := F.cochain K i
  d i := F.d K i
  d_sq := hdd
  N := Fintype.card K.ι
  hBound n hn := by
    haveI : IsEmpty (K.Idx n) := by
      refine ⟨fun s => ?_⟩
      have := Fintype.card_le_of_injective s.1 s.2.injective
      simp only [Fintype.card_fin] at this
      omega
    infer_instance

theorem ofCech_X {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) (i : ℕ) : (ofCech F K hdd).X i = F.cochain K i := rfl

theorem ofCech_d {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) (i : ℕ) : (ofCech F K hdd).d i = F.d K i := rfl

theorem ofCech_H_succ {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) (i : ℕ) : (ofCech F K hdd).H (i + 1) = F.HSucc K i := rfl

theorem ofCech_H_zero {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) :
    (ofCech F K hdd).H 0 = ((F.H0 K) ⧸ (⊥ : Submodule R (F.H0 K))) := rfl

end Bounded

end CochainCx

end
