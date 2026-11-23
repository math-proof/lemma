module

public import Mathlib
public import Class.AlgebraicCurve_DivisorClassGroup
public import Class.AlgebraicCurve_DivisorPushPull
public import Instance.DedekindDomain_AdicValuation_InlineSpecific
public import Abbrev.AlgebraicCurve_PlaceCompletion

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

namespace AlgebraicCurve.Place


section CompletionComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

def kw_ffgc_adicCompletionComap : (W.restrict F).adicCompletion →+* W.adicCompletion :=
  ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv F' W.heightOneSpectrum).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (WithVal.map ((W.restrict F).heightOneSpectrum.valuation F)
        (W.heightOneSpectrum.valuation F') (algebraMap F F'))
      (kw_ffgc_uniformContinuous_withValMapAlgebraMap F W).continuous)).comp
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv F (W.restrict F).heightOneSpectrum).toRingHom


end CompletionComap

end AlgebraicCurve.Place

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

namespace AlgebraicCurve.Place

section IntegerComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

def kw_ffgc_adicCompletionComapIntegers :
    (W.restrict F).adicCompletionIntegers →+* W.adicCompletionIntegers :=
  (kw_ffgc_adicCompletionComap F W).restrict _ _
    fun _ hx => kw_ffgc_adicCompletionComap_mem_integers F W hx

end IntegerComap

end AlgebraicCurve.Place

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open Polynomial IsLocalRing IsDedekindDomain

namespace AlgebraicCurve.Place


section SpectralSetup

open scoped Valued NNReal WithZero

open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

@[implicit_reducible]
noncomputable def kw_ffgc_rankOne_adicCompletion :
    (Valued.v : Valuation V.adicCompletion ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (one_lt_two (α := NNReal))

end SpectralSetup

section AbsoluteValue

open scoped Valued NNReal WithZero

open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

noncomputable def kw_ffgc_absoluteValue : AbsoluteValue W.adicCompletion ℝ :=
  letI := kw_ffgc_rankOne_adicCompletion W
  have hr : (0 : ℝ) < ((W.ramificationIndex F : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F)))
  { toFun := fun y => ‖y‖ ^ ((W.ramificationIndex F : ℝ))⁻¹
    map_mul' := fun x y => by rw [norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg y)]
    nonneg' := fun x => Real.rpow_nonneg (norm_nonneg x) _
    eq_zero' := fun x => by
      rw [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg x), norm_eq_zero]
      exact ⟨fun h => h.1, fun h => ⟨h, hr.ne'⟩⟩
    add_le' := fun x y => by
      have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := Valuation.norm_add_le Valued.v x y
      refine (Real.rpow_le_rpow (norm_nonneg _) hmax hr.le).trans ?_
      rcases max_cases ‖x‖ ‖y‖ with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
      · exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)
      · exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _) }

end AbsoluteValue


end AlgebraicCurve.Place

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

open scoped Valued WithZero

namespace AlgebraicCurve.Place

section FiniteDimensional

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

def kw_ffgc_completionLinearCombination {ι : Type*} [Fintype ι] (b : Module.Basis ι F F') :
    letI : Algebra (W.restrict F).adicCompletion W.adicCompletion :=
      (kw_ffgc_adicCompletionComap F W).toAlgebra
    (ι → (W.restrict F).adicCompletion)
      →ₗ[(W.restrict F).adicCompletion] W.adicCompletion :=
  letI : Algebra (W.restrict F).adicCompletion W.adicCompletion :=
    (kw_ffgc_adicCompletionComap F W).toAlgebra
  Fintype.linearCombination (W.restrict F).adicCompletion
    (fun i => algebraMap F' W.adicCompletion (b i))

end FiniteDimensional

section CompletionTrace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

def kw_ffgc_completionTraceF' [FiniteDimensional F F'] : F' →ₗ[F] (W.restrict F).adicCompletion :=
  letI : Algebra (W.restrict F).adicCompletion W.adicCompletion :=
    (kw_ffgc_adicCompletionComap F W).toAlgebra
  { toFun := fun g => kw_ffgc_completionTrace F W (algebraMap F' W.adicCompletion g)
    map_add' := fun x y => by simp only [map_add]
    map_smul' := fun c x => by
      simp only [Algebra.smul_def, map_mul, RingHom.id_apply,
        kw_ffgc_adicCompletionComap_algebraMap_algebraMap]
      rw [← Algebra.smul_def, LinearMap.map_smul, Algebra.smul_def]
      rfl }

end CompletionTrace

end AlgebraicCurve.Place

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain

noncomputable section


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

noncomputable section

namespace ModularCurve.KwF4gRRTate

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def algebraMapKIntegers : K →+* u.adicCompletionIntegers where
  toFun c := ⟨algebraMap K u.adicCompletion c, algebraMap_K_mem_adicCompletionIntegers u c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

end PoleWindowShift

end ModularCurve.KwF4gRRTate

end

end
end
end
end
end

end
