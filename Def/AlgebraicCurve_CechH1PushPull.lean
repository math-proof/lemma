module

public import Mathlib
public import Def.AlgebraicCurve_CechSectionsOfDivisor
public import Def.AlgebraicCurve_Correspondence

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def lSpaceOnZero.pullbackAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (S₀ S₁ : Set (Place K F)) :
    ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)) →ₗ[K]
      ↥(lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S₀ ∩ (Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F')) :=
  LinearMap.codRestrict _ (φ.toLinearMap.comp (lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)).subtype)
    (fun f => map_mem_lSpaceOn_preimage φ hφ f.2)

def cechH1.pullbackAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (S₀ S₁ : Set (Place K F)) :
    cechH1 S₀ S₁ (0 : Divisor K F) →ₗ[K]
      cechH1 ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F') :=
  Submodule.mapQ _ _ (lSpaceOnZero.pullbackAlong φ hφ S₀ S₁)
    (range_cechDiff_le_comap_pullbackAlong φ hφ S₀ S₁)

def traceFunAlong (φ : F →ₐ[K] F') : F' →ₗ[K] F :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  (Algebra.trace F F').restrictScalars K

def TraceIntegralAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : Prop :=
  ∀ (v : Place K F) (f' : F'),
    (∀ w : Place K F', w.restrictAlong φ hφ = v → f' ∈ w.toValuationSubring) →
      traceFunAlong φ f' ∈ v.toValuationSubring


def lSpaceOnZero.traceAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (htr : TraceIntegralAlong φ hφ) (S₀ S₁ : Set (Place K F)) :
    ↥(lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S₀ ∩ (Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F'))
      →ₗ[K] ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)) :=
  LinearMap.codRestrict _ ((traceFunAlong φ).comp (lSpaceOn _ (0 : Divisor K F')).subtype)
    (fun f' => traceFunAlong_mem_lSpaceOn htr (S := S₀ ∩ S₁)
      (by rw [Set.preimage_inter]; exact f'.2))

def cechH1.traceAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (htr : TraceIntegralAlong φ hφ)
    (S₀ S₁ : Set (Place K F)) :
    cechH1 ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F')
      →ₗ[K] cechH1 S₀ S₁ (0 : Divisor K F) :=
  Submodule.mapQ _ _ (lSpaceOnZero.traceAlong φ hφ htr S₀ S₁)
    (range_cechDiff_le_comap_traceAlong φ hφ htr S₀ S₁)

end AlgebraicCurve

end

end
