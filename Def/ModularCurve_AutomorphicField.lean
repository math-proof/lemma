module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped Manifold MatrixGroups Topology

namespace ModularCurve

def holRing : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  mul_mem' hf hg := hf.mul hg
  one_mem' := mdifferentiable_const
  add_mem' hf hg := hf.add hg
  zero_mem' := mdifferentiable_const
  algebraMap_mem' _ := mdifferentiable_const

def merRealize (x : FractionRing ↥holRing) : ℍ → ℂ := fun τ =>
  ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).1 : ℍ → ℂ) τ /
    (((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) : ℍ → ℂ) τ

end ModularCurve

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def toHolRing (f : ModularForm Γ k) : ↥ModularCurve.holRing := ⟨f, f.holo'⟩

end ModularForm

namespace ModularCurve

section

variable (Γ : Subgroup (GL (Fin 2) ℝ))

def automorphicRatioSet : Set (FractionRing ↥holRing) :=
  {x | ∃ (k : ℤ) (g h : ModularForm Γ k), (h : ℍ → ℂ) ≠ 0 ∧
    x = algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
          algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing}

variable {Γ}

variable [Γ.HasDetOne]

variable (Γ)

def automorphicField : Subfield (FractionRing ↥holRing) where
  carrier := automorphicRatioSet Γ
  mul_mem' := mul_mem_automorphicRatioSet
  one_mem' := one_mem_automorphicRatioSet
  add_mem' := add_mem_automorphicRatioSet
  zero_mem' := zero_mem_automorphicRatioSet
  neg_mem' := neg_mem_automorphicRatioSet
  inv_mem' _ := inv_mem_automorphicRatioSet

variable {Γ}

variable (Γ)

def automorphicField.constHom : ℂ →+* ↥(automorphicField Γ) :=
  ((algebraMap (↥holRing) (FractionRing ↥holRing)).comp (algebraMap ℂ ↥holRing)).codRestrict
    (automorphicField Γ) (fun c => by
      have h1 : ((1 : ModularForm Γ 0) : ℍ → ℂ) ≠ 0 := by
        rw [ModularForm.one_coe_eq_one]; exact one_ne_zero
      refine ⟨0, ModularForm.const c, 1, h1, ?_⟩
      have e1 : (1 : ModularForm Γ 0).toHolRing = 1 := Subtype.ext ModularForm.one_coe_eq_one
      have e2 : (ModularForm.const c : ModularForm Γ 0).toHolRing = algebraMap ℂ ↥holRing c :=
        Subtype.ext (funext fun τ => by simp [Algebra.algebraMap_eq_smul_one])
      rw [e1, RingHom.map_one, div_one, e2]
      rfl)

end

def automorphicField.realize {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (x : ↥(automorphicField Γ)) : ℍ → ℂ :=
  merRealize (x : FractionRing ↥holRing)

end ModularCurve

end

end
