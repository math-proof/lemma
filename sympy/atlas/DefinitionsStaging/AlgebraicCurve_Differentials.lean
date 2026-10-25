import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Kaehler.Basic
import Def.AlgebraicCurve_Differentials

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

open Classical in


theorem ord_uniformizer_alt (h : ∃ t : F, v.ord t = 1) : v.ord v.uniformizer_alt = 1 := by
  rw [uniformizer_alt, dif_pos h]
  exact h.choose_spec

open Classical in


theorem diffCoeff_smul_D {t : F} {ω : Ω[F⁄K]} (h : ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω • D K F t = ω := by
  rw [diffCoeff, dif_pos h]
  exact h.choose_spec.symm

theorem diffCoeff_of_not_exists {t : F} {ω : Ω[F⁄K]} (h : ¬ ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω = 0 := by
  rw [diffCoeff, dif_neg h]


theorem ordDiff_def (ω : Ω[F⁄K]) : v.ordDiff ω = v.ord (diffCoeff v.uniformizer_alt ω) := rfl

end Place

variable (K F) in


theorem isRegularDiff_iff (ω : Ω[F⁄K]) :
    IsRegularDiff K F ω ↔ ∀ v : Place K F, 0 ≤ v.ordDiff ω := Iff.rfl

variable (K F) in


theorem mem_regularDiffs_of_isRegularDiff {ω : Ω[F⁄K]} (h : IsRegularDiff K F ω) :
    ω ∈ regularDiffs K F :=
  Submodule.subset_span h

theorem regularDiffs_eq_span :
    regularDiffs K F = Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω} := rfl

section Pullback

variable {F' : Type*} [Field F'] [Algebra K F']


theorem pullbackDiff_D (φ : F →ₐ[K] F') (x : F) :
    pullbackDiff φ (D K F x) = D K F' (φ x) := by
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  exact KaehlerDifferential.map_D K K F F' x

end Pullback

end AlgebraicCurve

end
