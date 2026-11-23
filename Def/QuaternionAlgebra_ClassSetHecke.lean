module

public import Mathlib
public import Theorem.Submodule.FiniteAdeleBox
public import Def.QuaternionAlgebra_Order
public import Theorem.QuaternionAlgebra.ReducedNorm
public import Abbrev.QuaternionAlgebra_ClassSetHecke

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra

variable {a b : ℚ}

namespace ClassSet

variable {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

def map (h : U ≤ U') : ClassSet U → ClassSet U' :=
  Quotient.map' id fun x y hxy => by
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.rel_iff.mp hxy
    exact DoubleCoset.rel_iff.mpr ⟨c, hc, d, h hd, rfl⟩

end ClassSet

section HeckeKernel

def HeckeIncidence (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) : Type :=
  {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U //
    ∃ h ∈ S, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c ∧ ClassSet.mk U (x * h) = y}

def heckeKernel (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U) : ℤ :=
  Nat.card (HeckeIncidence U S x.out y)

def heckeIncidenceEquiv (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ U) (y : ClassSet U) :
    HeckeIncidence U S (x * u) y ≃ HeckeIncidence U S x y where
  toFun c := ⟨u • c.1, by
    obtain ⟨h, hh, hc, hy⟩ := c.2
    refine ⟨u * h, hS u hu h hh, ?_, ?_⟩
    · rw [← hc]; rfl
    · rwa [← mul_assoc]⟩
  invFun c := ⟨u⁻¹ • c.1, by
    obtain ⟨h, hh, hc, hy⟩ := c.2
    refine ⟨u⁻¹ * h, hS u⁻¹ (inv_mem hu) h hh, ?_, ?_⟩
    · rw [← hc]; rfl
    · rwa [← mul_assoc, mul_inv_cancel_right]⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)

end HeckeKernel

section Level

def primeHeckeSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {h | (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
    (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
    ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
        ∉ Submodule.finiteAdeleBox Λ ∧
    (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∉ Submodule.finiteAdeleBox Λ}

def levelHeckeSet (Λ P : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  primeHeckeSet Λ ℓ ∩
    {h | (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ Submodule.finiteAdeleBox P}

def congruenceLevel (Λ P : Submodule ℤ ℍ[ℚ, a, b]) :
    Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ where
  carrier := {u | u ∈ Submodule.finiteIdeleStabilizer Λ ∧ u ∈ Submodule.finiteIdeleStabilizer P ∧
    ∀ x ∈ Submodule.finiteAdeleBox Λ,
      (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x ∈ Submodule.finiteAdeleBox P}
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro u v ⟨huΛ, huP, hu⟩ ⟨hvΛ, hvP, hv⟩
    refine ⟨mul_mem huΛ hvΛ, mul_mem huP hvP, fun x hx => ?_⟩
    have h1 : (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ((v : _) * x - x) ∈
        Submodule.finiteAdeleBox P := by
      have hmem : (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ((v : _) * x - x) ∈
          u • ((Submodule.finiteAdeleBox P : AddSubgroup _) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
        Set.smul_mem_smul_set (hv x hx)
      rwa [(Submodule.mem_finiteIdeleStabilizer_iff P u).mp huP] at hmem
    have h2 := hu x hx
    have : ((u * v : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x
        = (u : _) * ((v : _) * x - x) + ((u : _) * x - x) := by
      rw [Units.val_mul, mul_sub, mul_assoc]; abel
    rw [this]
    exact add_mem h1 h2
  inv_mem' := by
    rintro u ⟨huΛ, huP, hu⟩
    refine ⟨inv_mem huΛ, inv_mem huP, fun x hx => ?_⟩
    have hy : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) * x ∈
        Submodule.finiteAdeleBox Λ := by
      have hmem : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) * x ∈
          u⁻¹ • ((Submodule.finiteAdeleBox Λ : AddSubgroup _) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
        Set.smul_mem_smul_set hx
      rwa [(Submodule.mem_finiteIdeleStabilizer_iff Λ u⁻¹).mp (inv_mem huΛ)] at hmem
    have h := hu _ hy
    rw [← mul_assoc, Units.mul_inv, one_mul] at h
    rw [← neg_sub]
    exact neg_mem h

def normIdeal (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) : Submodule ℤ ℍ[ℚ, a, b] :=
  Submodule.span ℤ {w | ∃ x ∈ Λ, ∃ y ∈ Λ, ∃ z ∈ Λ, (∃ m : ℤ, nrd y = (q : ℚ) * m) ∧ w = x * y * z}

end Level

end QuaternionAlgebra

end

end
