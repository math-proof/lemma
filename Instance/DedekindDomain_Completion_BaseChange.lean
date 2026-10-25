-- Carved from Lemma/Definitions/Def_DedekindDomain_Completion_BaseChange.lean: instance decls only.
import Instance.DedekindDomain_AdicValuation_InlineSpecific
import Class.Mathlib_IsModuleTopology

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

set_option maxSynthPendingDepth 3
set_option Elab.async false

section

variable {R S : Type*} [Ring R]


section


section
open scoped TensorProduct
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}

noncomputable


instance [Algebra R S] [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    IsBiscalar S A ψ.baseChange_of_algebraMap where
  __ := ψ.toAlgebra
  map_smul₁ s x := ψ.baseChange_of_algebraMap.map_smul_of_tower ..
  map_smul₂ a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [TensorProduct.smul_tmul', -algebraMap_smul,
        algebra_compatible_smul B a, SemialgHom.baseChange_of_algebraMap_tmul,
        RingHom.algebraMap_toAlgebra, SemialgHom.toLinearMap_eq_coe]
      ring
    | add x y hx hy => simp_all

open scoped TensorProduct.RightActions in

noncomputable


section


section

open scoped WithZero Valued TensorProduct
open Valuation.IsRankOneDiscrete WithZero

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]


variable [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

namespace IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum A) {A B}

noncomputable instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  LieAlgebra.ofAssociativeAlgebra.toMulAction

instance (w : v.Extension B) [FiniteDimensional K L] [Module.Finite A B] :
    Module.Free (v.adicCompletion K) (adicCompletion L w.1) :=
  Module.free_of_finite_type_torsion_free'

local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))


namespace Extension

variable {v} (w : v.Extension B)


instance : Algebra (v.adicCompletion K) (w.1.adicCompletion L) :=
  (w.adicCompletionSemialgHom K L).toAlgebra


instance : ContinuousSMul (adicCompletion K v) (adicCompletion L w.1) := by
  constructor
  have leftCts := w.adicCompletionSemialgHom_continuous K L
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd

end Extension

section shortcut_instances

private noncomputable instance : Valued (v.adicCompletion K) ℤᵐ⁰ := inferInstance
private noncomputable instance : Field (v.adicCompletion K) := inferInstance
private noncomputable instance : CommRing (v.adicCompletion K) := inferInstance
private noncomputable instance : Ring (v.adicCompletion K) := inferInstance
private noncomputable instance : CommSemiring (v.adicCompletion K) := inferInstance
private noncomputable instance : Semiring (v.adicCompletion K) := inferInstance
private noncomputable instance : AddCommGroup (v.adicCompletion K) := inferInstance
private noncomputable instance : AddCommMonoid (v.adicCompletion K) := inferInstance

private noncomputable instance (w : v.Extension B) : Valued (w.1.adicCompletion L) ℤᵐ⁰ := inferInstance
private noncomputable instance (w : v.Extension B) : Field (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : CommRing (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Ring (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : CommSemiring (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Semiring (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : AddCommGroup (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : AddCommMonoid (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Algebra (v.adicCompletion K) (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Module (v.adicCompletion K) (w.1.adicCompletion L) := inferInstance

private noncomputable instance : CommRing (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Ring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : CommSemiring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Semiring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : AddCommGroup (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : AddCommMonoid (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Algebra (v.adicCompletion K) (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Module (v.adicCompletion K) (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Algebra L (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private instance : IsTopologicalRing (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private instance : IsTopologicalAddGroup (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

end shortcut_instances

namespace adicCompletion

variable (B)


section ModuleTopology

open WithZeroMulInt Valued in

noncomputable local instance :
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤᵐ⁰) where
  hom' := (toNNReal (by norm_num : (2 : NNReal) ≠ 0)).comp
    (valueGroup₀_equiv_withZeroMulInt _).toMonoidWithZeroHom
  strictMono' := toNNReal_strictMono (by norm_num) |>.comp
    (valueGroup₀_equiv_withZeroMulInt_strictMono _)
  exists_val_nontrivial := by
    obtain ⟨x, hx1, hx2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    use algebraMap A K x
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_of_algebraMap, intValuation_lt_one_iff_mem]

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in


instance [FiniteDimensional K L] :
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) :=
  .of_surjective (baseChangeRight K L B v).toLinearMap (baseChangeRight_surjective K L B v)

attribute [local instance 9999] Algebra.toModule in

instance [FiniteDimensional K L] (w : v.Extension B) :
    Module.Finite (adicCompletion K v) (adicCompletion L w.1) :=
  Module.Finite.of_pi (fun (w : Extension B v) => w.1.adicCompletion L) w

instance instIsModuleTopology [FiniteDimensional K L] (w : v.Extension B) :
    IsModuleTopology (v.adicCompletion K) (w.1.adicCompletion L) := by
  let Kv := adicCompletion K v
  let Lw := adicCompletion L w.1
  let iso : ((Fin (Module.finrank Kv Lw)) → Kv) ≃L[Kv] Lw :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Kv)
  apply IsModuleTopology.iso iso

instance instIsModuleTopologyPi [FiniteDimensional K L] :

    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := by
  let := Extension.finite A K L B v
  exact IsModuleTopology.instPi

open scoped TensorProduct.RightActions in


end ModuleTopology

end adicCompletion

section ModuleTopology

open Extension adicCompletion

variable (B)


instance : MulActionHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1) B
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
  map_smulₛₗ φ b x := by
    rw [← IsScalarTower.algebraMap_smul L, AlgHom.map_smul_of_tower,
      IsScalarTower.algebraMap_smul, id_def]

open scoped TensorProduct.RightActions in


namespace Extension

variable {B} (w : v.Extension B)


noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  (w.adicCompletionIntegersRingHom K L).toAlgebra


noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Algebra.compHom (w.1.adicCompletion L) (algebraMap _ (adicCompletion K v))

end Extension

open scoped TensorProduct.RightActions in
instance : IsBiscalar B (v.adicCompletionIntegers K) (tensorAdicCompletionIntegersTo K L B v) where
  map_smul₁ _ _ := map_smul ..
  map_smul₂ _ _ := by
    simp only [tensorAdicCompletionIntegersTo_tmul, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, map_mul, map_one]
    rfl

attribute [local instance 9999] Algebra.toModule Algebra.toSMul in
instance {w : v.Extension B} : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v)
    (w.1.adicCompletion L) := Submonoid.instIsScalarTowerSubtypeMem (adicCompletionIntegers K v)

open scoped TensorProduct.RightActions in


namespace Extension

variable (w : v.Extension B)

open scoped TensorProduct.RightActions in


noncomputable instance (priority := 1001) [Module.Finite A B] [FiniteDimensional K L] :
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
  let integerSubmodule : Submodule (adicCompletionIntegers K v) (adicCompletion L w.1) :=
    let : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
        (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
    (adicCompletionIntegers L w.1).toSubmodule.restrictScalars
      (adicCompletionIntegers K v)
  have heq : (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap.range =
      integerSubmodule := by
    ext x
    apply w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v |> Set.ext_iff.mp
  have := Module.Finite.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap
  have := w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v
  exact Module.Finite.equiv <| LinearEquiv.ofEq
    (LinearMap.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap) _ heq

end Extension

end ModuleTopology


namespace adicCompletion

open Extension

variable [FiniteDimensional K L] [Module.Finite A B]

attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
  IsScalarTower.right in
end adicCompletion
end IsDedekindDomain.HeightOneSpectrum
end
end
end
end
end
