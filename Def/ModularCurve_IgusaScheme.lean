module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.Polynomial.Lifts
public import Theorem.HahnSeries.X0
public import Def.GaloisRep_Flat
public import Notation.ModularCurve_IgusaScheme
set_option autoImplicit false


public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace ModularCurve

namespace IgusaScheme

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]


open scoped ModularCurve_IgusaScheme

set_option quotPrecheck false in


def jFull : F := ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩

def chartAlg (S : Set F) : Subalgebra ℤℓ F where
  carrier := {x | IsIntegral (Algebra.adjoin ℤℓ S) x}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isIntegral_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  algebraMap_mem' a := by
    have : IsIntegral (Algebra.adjoin ℤℓ S)
        (algebraMap (Algebra.adjoin ℤℓ S) F (algebraMap ℤℓ (Algebra.adjoin ℤℓ S) a)) :=
      isIntegral_algebraMap
    simpa [← IsScalarTower.algebraMap_apply] using this

abbrev chartIncl {S S' : Set F} (h : S ⊆ S') : chartAlg N ℓ S →ₐ[ℤℓ] chartAlg N ℓ S' :=
  Subalgebra.inclusion (chartAlg_mono N ℓ h)

variable {N ℓ}

variable (N ℓ)

abbrev chartAlgFin : Subalgebra ℤℓ F := chartAlg N ℓ {jFull N}

abbrev chartAlgInf : Subalgebra ℤℓ F := chartAlg N ℓ {(jFull N)⁻¹}

abbrev chartAlgMid : Subalgebra ℤℓ F := chartAlg N ℓ {jFull N, (jFull N)⁻¹}

def jChartFin : chartAlgFin N ℓ := ⟨jFull N, subset_chartAlg N ℓ _ rfl⟩

def jInvChartInf : chartAlgInf N ℓ := ⟨(jFull N)⁻¹, subset_chartAlg N ℓ _ rfl⟩

abbrev inclFin : chartAlgFin N ℓ →ₐ[ℤℓ] chartAlgMid N ℓ := chartIncl N ℓ (sFin_subset N)

abbrev inclInf : chartAlgInf N ℓ →ₐ[ℤℓ] chartAlgMid N ℓ := chartIncl N ℓ (sInf_subset N)

abbrev XFin : Scheme.{0} := Spec (CommRingCat.of (chartAlgFin N ℓ))

abbrev XInf : Scheme.{0} := Spec (CommRingCat.of (chartAlgInf N ℓ))

abbrev XMid : Scheme.{0} := Spec (CommRingCat.of (chartAlgMid N ℓ))

abbrev fFin : XMid N ℓ ⟶ XFin N ℓ := Spec.map (CommRingCat.ofHom (inclFin N ℓ).toRingHom)

abbrev fInf : XMid N ℓ ⟶ XInf N ℓ := Spec.map (CommRingCat.ofHom (inclInf N ℓ).toRingHom)

def _root_.Scheme.IgusaScheme : Scheme.{0} := pushout (fFin N ℓ) (fInf N ℓ)

def ιFin : XFin N ℓ ⟶ Scheme.IgusaScheme N ℓ := pushout.inl (fFin N ℓ) (fInf N ℓ)

def ιInf : XInf N ℓ ⟶ Scheme.IgusaScheme N ℓ := pushout.inr (fFin N ℓ) (fInf N ℓ)

def igusaTo : Scheme.IgusaScheme N ℓ ⟶ Spec (CommRingCat.of ℤℓ) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgFin N ℓ))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgInf N ℓ))))
    (fFin_toBase_eq_fInf_toBase N ℓ)

def chartFinOpen : (Scheme.IgusaScheme N ℓ).Opens := (ιFin N ℓ).opensRange

def chartInfOpen : (Scheme.IgusaScheme N ℓ).Opens := (ιInf N ℓ).opensRange

end IgusaScheme

end ModularCurve

end
