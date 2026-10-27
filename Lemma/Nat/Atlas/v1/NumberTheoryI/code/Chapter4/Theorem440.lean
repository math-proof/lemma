import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Chapter4.Theorem440
open EtaleAlgebra Polynomial IntermediateField
open scoped TensorProduct
open Polynomial IntermediateField EtaleAlgebra


/--
[formallyUnramified_baseChange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/Theorem440.lean)
-/
@[path]
lemma formallyUnramified_baseChange
  {K : Type u}
  [Field K]
  {B : Type v}
  [CommRing B]
  [Algebra K B]
  [Module.Finite K B]
  [Field K]
  [CommRing B]
  [Algebra K B]
  [Algebra.FormallyUnramified K B]
  [CommRing Ω]
  [Algebra K Ω] :
-- imply
  Algebra.FormallyUnramified Ω (Ω ⊗[K] B) := by
-- proof
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro C _ _ I hI
  letI : Algebra K C := (algebraMap Ω C).comp (algebraMap K Ω) |>.toAlgebra
  haveI : IsScalarTower K Ω C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro f₁ f₂ he
  apply Algebra.TensorProduct.ext
  · ext
  · exact Algebra.FormallyUnramified.comp_injective I hI (by
    ext b; simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    exact AlgHom.congr_fun he (1 ⊗ₜ b))

/--
[sep_tensor_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/Theorem440.lean)
-/
@[path]
lemma sep_tensor_reduced
  {K : Type u}
  [Field K]
  {B : Type v}
  [CommRing B]
  [Algebra K B]
  [Module.Finite K B]
  {K : Type*}
  [Field K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra.IsSeparable K L]
  {Ω : Type*}
  [Field Ω]
  [Algebra K Ω] :
-- imply
  IsReduced (L ⊗[K] Ω) := by
-- proof
  suffices h : IsReduced (Ω ⊗[K] L) from
    isReduced_of_injective
      (Algebra.TensorProduct.comm K L Ω).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm K L Ω).toRingEquiv.injective
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hfg
  haveI : Algebra.IsIntegral K L := ⟨Algebra.IsSeparable.isIntegral K⟩
  haveI : Algebra.IsIntegral K B := Algebra.IsIntegral.of_injective B.val Subtype.val_injective
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  haveI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).mp hfg
  haveI : Module.Finite K B := Algebra.IsIntegral.finite
  letI : Field B := (isField_of_isIntegral_of_isField' (Field.toIsField K)).toField
  haveI : Algebra.IsSeparable K B := Algebra.IsSeparable.of_algHom K L B.val
  haveI : Algebra.FormallyUnramified K B := Algebra.FormallyUnramified.of_isSeparable K B
  haveI : Algebra.FormallyUnramified Ω (Ω ⊗[K] B) := formallyUnramified_baseChange
  haveI : Module.Finite Ω (Ω ⊗[K] B) := Module.Finite.base_change K Ω B
  haveI : Algebra.EssFiniteType Ω (Ω ⊗[K] B) :=
    Algebra.EssFiniteType.of_finiteType Ω (Ω ⊗[K] B)
  exact Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[K] B)

/--
[isReduced_pi_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/Theorem440.lean)
-/
@[path]
lemma isReduced_pi_tensor
  {K : Type u}
  [Field K]
  {B : Type v}
  [CommRing B]
  [Algebra K B]
  [Module.Finite K B]
  {K : Type*}
  [Field K]
  {ι : Type}
  [Fintype ι]
  {F : ι → Type}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  [∀ i, Algebra.IsSeparable K (F i)]
  {Ω : Type*}
  [Field Ω]
  [Algebra K Ω] :
-- imply
  IsReduced ((∀ i, F i) ⊗[K] Ω) := by
-- proof
  classical
  let e := (Algebra.TensorProduct.comm K (∀ i, F i) Ω).toRingEquiv.trans
    (Algebra.TensorProduct.piRight K Ω Ω F).toRingEquiv
  haveI : ∀ i, IsReduced (Ω ⊗[K] F i) := fun i => by
    haveI := sep_tensor_reduced K (F i) Ω
    exact isReduced_of_injective
      (Algebra.TensorProduct.comm K (F i) Ω).toRingEquiv.symm.toRingHom
      (Algebra.TensorProduct.comm K (F i) Ω).toRingEquiv.symm.injective
  exact isReduced_of_injective e.toRingHom e.injective
noncomputable section EtaleFieldExtensions
open scoped TensorProduct
open Polynomial IntermediateField EtaleAlgebra
end EtaleFieldExtensions


-- created on 2026-10-23
