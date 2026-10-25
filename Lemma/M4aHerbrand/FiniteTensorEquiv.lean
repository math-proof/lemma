import Lemma.M4aHerbrand.FiniteConorm
import Lemma.DedekindDomain.FiniteAdeleRing_TensorRestrictedProduct
import Lemma.Topology.Algebra.RestrictedProduct.Equiv
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section

namespace M4aHerbrand.Bridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TensorProduct RestrictedProduct

open scoped TensorProduct RestrictedProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

section AKLB

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
    [FiniteDimensional K L] [Module.Finite A B]

section shortcut_instances

variable (v : HeightOneSpectrum A) (w' : HeightOneSpectrum B)


end shortcut_instances

theorem finiteAdeleRing_mul_apply (x y : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    (x * y) v = x v * y v := rfl

theorem finiteAdeleRing_one_apply (v : HeightOneSpectrum A) : (1 : FiniteAdeleRing A K) v = 1 := rfl

def moduleStructureBridge :
    (FiniteAdeleRing A K) ≃ₗ[A]
      (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, adicCompletion.integerSubmodule K v]) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    ext v : 1
    change ((a • x : FiniteAdeleRing A K) v) = a • (x v)
    rw [Algebra.smul_def a (x v)]
    rw [show (a • x : FiniteAdeleRing A K) = algebraMap A (FiniteAdeleRing A K) a * x from
      Algebra.smul_def a x]
    rw [finiteAdeleRing_mul_apply]
    congr 1
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem moduleStructureBridge_apply (x : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    moduleStructureBridge A K x v = x v := rfl

include K L in
omit [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [FiniteDimensional K L] [Module.Finite A B] in
theorem flat_of_aklb : Module.Flat A B := by
  haveI := HeightOneSpectrum.isTorsionFree A K L B
  infer_instance

def tensorComponents :
    (B ⊗[A] (FiniteAdeleRing A K)) ≃ₗ[B]
      (Πʳ v : HeightOneSpectrum A, [B ⊗[A] (v.adicCompletion K),
        rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) v]) :=
  haveI := flat_of_aklb A K L B
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (moduleStructureBridge A K)).trans
    (lTensorEquivLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
      (fun u => adicCompletion.integerSubmodule K u) Filter.cofinite)

omit [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [FiniteDimensional K L] in
theorem tensorComponents_tmul (b : B) (x : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    tensorComponents A K L B (b ⊗ₜ x) v = b ⊗ₜ (x v) := by
  haveI := flat_of_aklb A K L B
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  rw [show tensorComponents A K L B (b ⊗ₜ x)
      = lTensorEquivLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) Filter.cofinite
          ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
            (moduleStructureBridge A K)) (b ⊗ₜ x)) from rfl]
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, lTensorEquivLeft_tmul,
    moduleStructureBridge_apply]

set_option maxHeartbeats 800000 in
omit [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [FiniteDimensional K L] in
theorem tensorComponents_mul_apply (z₁ z₂ : B ⊗[A] (FiniteAdeleRing A K)) (v : HeightOneSpectrum A) :
    tensorComponents A K L B (z₁ * z₂) v
      = tensorComponents A K L B z₁ v * tensorComponents A K L B z₂ v := by
  induction z₁ using TensorProduct.induction_on with
  | zero =>
    rw [zero_mul, map_zero, RestrictedProduct.zero_apply, zero_mul]
  | add u₁ u₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, RestrictedProduct.add_apply, RestrictedProduct.add_apply,
      h₁, h₂, add_mul]
  | tmul b₁ x₁ =>
    induction z₂ using TensorProduct.induction_on with
    | zero =>
      rw [mul_zero, map_zero, RestrictedProduct.zero_apply, mul_zero]
    | add u₁ u₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, RestrictedProduct.add_apply, RestrictedProduct.add_apply,
        h₁, h₂, mul_add]
    | tmul b₂ x₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tensorComponents_tmul, tensorComponents_tmul,
        tensorComponents_tmul, finiteAdeleRing_mul_apply, Algebra.TensorProduct.tmul_mul_tmul]

omit [IsIntegralClosure B A L] in

theorem integerBaseChangeLinearEquiv_mul (v : HeightOneSpectrum A) (s t : B ⊗[A] (v.adicCompletion K)) :
    adicCompletion.integerBaseChangeLinearEquiv K L B v (s * t) =
      adicCompletion.integerBaseChangeLinearEquiv K L B v s *
        adicCompletion.integerBaseChangeLinearEquiv K L B v t := by
  induction s using TensorProduct.induction_on with
  | zero => rw [zero_mul, LinearEquiv.map_zero, zero_mul]
  | add u₁ u₂ h₁ h₂ => rw [add_mul, LinearEquiv.map_add, h₁, h₂, LinearEquiv.map_add, add_mul]
  | tmul b₁ x₁ =>
    induction t using TensorProduct.induction_on with
    | zero => rw [mul_zero, LinearEquiv.map_zero, mul_zero]
    | add u₁ u₂ h₁ h₂ => rw [mul_add, LinearEquiv.map_add, h₁, h₂, LinearEquiv.map_add, mul_add]
    | tmul b₂ x₂ =>
      funext w
      rw [Algebra.TensorProduct.tmul_mul_tmul, Pi.mul_apply,
        adicCompletion.integerBaseChangeLinearEquiv_tmul_apply,
        adicCompletion.integerBaseChangeLinearEquiv_tmul_apply,
        adicCompletion.integerBaseChangeLinearEquiv_tmul_apply, RingHom.map_mul, RingHom.map_mul]
      ring

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [Module.Finite A B] in

theorem rangeLTensorLeft_eq_range_tensorCoe (v : HeightOneSpectrum A) :
    ((rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
        (fun u => adicCompletion.integerSubmodule K u) v :
          Submodule B (B ⊗[A] (v.adicCompletion K))) : Set (B ⊗[A] (v.adicCompletion K))) =
      Set.range (adicCompletionIntegers.tensorCoe K B v) := by
  rw [← LinearMap.coe_range]
  refine SetLike.coe_set_eq.mpr ?_
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add u₁ u₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | tmul b y =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      exact ⟨b ⊗ₜ ⟨y.1, y.2⟩, rfl⟩
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add u₁ u₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | tmul b y =>
      rw [adicCompletionIntegers.tensorCoe_tmul]
      exact ⟨b ⊗ₜ ⟨y.1, y.2⟩, rfl⟩

omit [Algebra A L] [IsScalarTower A B L] [IsIntegralClosure B A L] [Module.Finite A B] in

theorem coe_pi_integerSubmodule (v : HeightOneSpectrum A) :
    ((Submodule.pi Set.univ fun (w : v.Extension B) => adicCompletion.integerSubmodule L w.1 :
        Submodule B ((w : v.Extension B) → w.1.adicCompletion L)) :
          Set ((w : v.Extension B) → w.1.adicCompletion L)) =
      Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) :=
  Set.ext fun _ => Iff.rfl

omit [IsIntegralClosure B A L] in

theorem integerBaseChangeLinearEquiv_bijOn' (v : HeightOneSpectrum A) :
    Set.BijOn (adicCompletion.integerBaseChangeLinearEquiv K L B v)
      ((rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
        (fun u => adicCompletion.integerSubmodule K u) v :
          Submodule B (B ⊗[A] (v.adicCompletion K))) : Set (B ⊗[A] (v.adicCompletion K)))
      (Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))) := by
  rw [rangeLTensorLeft_eq_range_tensorCoe, ← coe_pi_integerSubmodule]
  exact adicCompletion.integerBaseChangeLinearEquiv_bijOn K L v

def congrPlaces :
    (Πʳ v : HeightOneSpectrum A, [B ⊗[A] (v.adicCompletion K),
        rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) v])
      ≃ (Πʳ v : HeightOneSpectrum A, [(w : v.Extension B) → w.1.adicCompletion L,
        Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))]) :=
  Equiv.restrictedProductCongrRight
    (fun v => (adicCompletion.integerBaseChangeLinearEquiv K L B v).toEquiv)
    (Filter.Eventually.of_forall fun v => integerBaseChangeLinearEquiv_bijOn' A K L B v)

omit [IsIntegralClosure B A L] in
@[simp] theorem congrPlaces_apply
    (x : Πʳ v : HeightOneSpectrum A, [B ⊗[A] (v.adicCompletion K),
        rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) v])
    (v : HeightOneSpectrum A) :
    congrPlaces A K L B x v = adicCompletion.integerBaseChangeLinearEquiv K L B v (x v) := rfl

def flattenPlaces :
    (Πʳ v : HeightOneSpectrum A, [(w : v.Extension B) → w.1.adicCompletion L,
        Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))])
      ≃ FiniteAdeleRing B L :=
  RestrictedProduct.flatten_equiv'
    (fun w : HeightOneSpectrum B => ((w.adicCompletionIntegers L : Set (w.adicCompletion L))))
    (tendsto_under_cofinite A K L B)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B] in
@[simp] theorem flattenPlaces_apply
    (x : Πʳ v : HeightOneSpectrum A, [(w : v.Extension B) → w.1.adicCompletion L,
        Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))])
    (w : HeightOneSpectrum B) :
    flattenPlaces A K L B x w = x (w.under A) (⟨w, rfl⟩ : (w.under A).Extension B) := rfl

def tensorAdeleEquiv : (B ⊗[A] (FiniteAdeleRing A K)) ≃ (FiniteAdeleRing B L) :=
  (tensorComponents A K L B).toEquiv.trans ((congrPlaces A K L B).trans (flattenPlaces A K L B))

omit [IsIntegralClosure B A L] in
theorem tensorAdeleEquiv_apply (z : B ⊗[A] (FiniteAdeleRing A K)) (w : HeightOneSpectrum B) :
    tensorAdeleEquiv A K L B z w =
      adicCompletion.integerBaseChangeLinearEquiv K L B (w.under A)
        (tensorComponents A K L B z (w.under A)) (⟨w, rfl⟩ : (w.under A).Extension B) := rfl

def tensorAdeleRingEquiv : (B ⊗[A] (FiniteAdeleRing A K)) ≃+* (FiniteAdeleRing B L) where
  toEquiv := tensorAdeleEquiv A K L B
  map_mul' z₁ z₂ := by
    show tensorAdeleEquiv A K L B (z₁ * z₂) = tensorAdeleEquiv A K L B z₁ * tensorAdeleEquiv A K L B z₂
    apply FiniteAdeleRing.ext
    intro w
    rw [finiteAdeleRing_mul_apply, tensorAdeleEquiv_apply, tensorAdeleEquiv_apply, tensorAdeleEquiv_apply,
      tensorComponents_mul_apply, integerBaseChangeLinearEquiv_mul, Pi.mul_apply]
  map_add' z₁ z₂ := by
    show tensorAdeleEquiv A K L B (z₁ + z₂) = tensorAdeleEquiv A K L B z₁ + tensorAdeleEquiv A K L B z₂
    apply FiniteAdeleRing.ext
    intro w
    rw [show ((tensorAdeleEquiv A K L B z₁ + tensorAdeleEquiv A K L B z₂ : FiniteAdeleRing B L) w)
        = tensorAdeleEquiv A K L B z₁ w + tensorAdeleEquiv A K L B z₂ w from rfl,
      tensorAdeleEquiv_apply, tensorAdeleEquiv_apply, tensorAdeleEquiv_apply, map_add,
      RestrictedProduct.add_apply, map_add, Pi.add_apply]

omit [IsIntegralClosure B A L] in
@[simp] theorem tensorAdeleRingEquiv_apply (z : B ⊗[A] (FiniteAdeleRing A K)) :
    tensorAdeleRingEquiv A K L B z = tensorAdeleEquiv A K L B z := rfl

omit [IsIntegralClosure B A L] in
theorem tensorAdeleRingEquiv_tmul_apply (b : B) (x : FiniteAdeleRing A K) (w : HeightOneSpectrum B) :
    tensorAdeleRingEquiv A K L B (b ⊗ₜ x) w =
      algebraMap B (w.adicCompletion L) b *
        Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) (x (w.under A)) := by
  rw [tensorAdeleRingEquiv_apply, tensorAdeleEquiv_apply, tensorComponents_tmul,
    adicCompletion.integerBaseChangeLinearEquiv_tmul_apply]
  rfl

omit [IsIntegralClosure B A L] in
theorem tensorAdeleRingEquiv_one_tmul (x : FiniteAdeleRing A K) :
    tensorAdeleRingEquiv A K L B ((1 : B) ⊗ₜ x) = finiteConorm A K L B x := by
  apply FiniteAdeleRing.ext
  intro w
  rw [tensorAdeleRingEquiv_tmul_apply, map_one, one_mul, finiteConorm_apply]

def integralTensorRingEquiv : (B ⊗[A] (FiniteAdeleRing A K)) ≃+* (L ⊗[K] (FiniteAdeleRing A K)) where
  toFun := (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K)).symm
  invFun := (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K))
  left_inv z :=
    (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K)).apply_symm_apply z
  right_inv z :=
    (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K)).symm_apply_apply z
  map_add' z₁ z₂ := map_add _ z₁ z₂
  map_mul' z₁ z₂ := by
    induction z₁ using TensorProduct.induction_on with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | add u₁ u₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
    | tmul b₁ m₁ =>
      induction z₂ using TensorProduct.induction_on with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | add u₁ u₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
      | tmul b₂ m₂ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul,
          IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul,
          IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul,
          IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, map_mul]

omit [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B] [Module.Finite A B] in
@[simp] theorem integralTensorRingEquiv_tmul (b : B) (m : FiniteAdeleRing A K) :
    integralTensorRingEquiv A K L B (b ⊗ₜ m) = (algebraMap B L b) ⊗ₜ m :=
  IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul A K L B (FiniteAdeleRing A K) b m

omit [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B] [Module.Finite A B] in
theorem integralTensorRingEquiv_symm_algebraMap_tmul (b : B) (m : FiniteAdeleRing A K) :
    (integralTensorRingEquiv A K L B).symm ((algebraMap B L b) ⊗ₜ m) = b ⊗ₜ m := by
  rw [RingEquiv.symm_apply_eq, integralTensorRingEquiv_tmul]

omit [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B] [Module.Finite A B] in
theorem integralTensorRingEquiv_symm_one_tmul (m : FiniteAdeleRing A K) :
    (integralTensorRingEquiv A K L B).symm ((1 : L) ⊗ₜ m) = (1 : B) ⊗ₜ m := by
  have h := integralTensorRingEquiv_symm_algebraMap_tmul A K L B 1 m
  rwa [map_one] at h

def finiteBaseChangeRingEquiv : ((FiniteAdeleRing A K) ⊗[K] L) ≃+* (FiniteAdeleRing B L) :=
  ((Algebra.TensorProduct.comm K (FiniteAdeleRing A K) L).toRingEquiv.trans
    (integralTensorRingEquiv A K L B).symm).trans (tensorAdeleRingEquiv A K L B)

theorem finiteBaseChangeRingEquiv_apply (z : (FiniteAdeleRing A K) ⊗[K] L) :
    finiteBaseChangeRingEquiv A K L B z =
      tensorAdeleRingEquiv A K L B ((integralTensorRingEquiv A K L B).symm
        ((Algebra.TensorProduct.comm K (FiniteAdeleRing A K) L) z)) := rfl

theorem finiteBaseChangeRingEquiv_tmul_one (x : FiniteAdeleRing A K) :
    finiteBaseChangeRingEquiv A K L B (x ⊗ₜ (1 : L)) = finiteConorm A K L B x := by
  rw [finiteBaseChangeRingEquiv_apply, Algebra.TensorProduct.comm_tmul,
    integralTensorRingEquiv_symm_one_tmul, tensorAdeleRingEquiv_one_tmul]

theorem finiteBaseChangeRingEquiv_one_tmul_algebraMap (b : B) :
    finiteBaseChangeRingEquiv A K L B ((1 : FiniteAdeleRing A K) ⊗ₜ (algebraMap B L b)) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap B L b) := by
  rw [finiteBaseChangeRingEquiv_apply, Algebra.TensorProduct.comm_tmul,
    integralTensorRingEquiv_symm_algebraMap_tmul]
  apply FiniteAdeleRing.ext
  intro w
  rw [tensorAdeleRingEquiv_tmul_apply, finiteAdeleRing_one_apply, map_one, mul_one,
    FiniteAdeleRing.algebraMap_apply, IsScalarTower.algebraMap_apply B L (w.adicCompletion L)]
  rfl

theorem finiteBaseChangeRingEquiv_one_tmul (l : L) :
    finiteBaseChangeRingEquiv A K L B ((1 : FiniteAdeleRing A K) ⊗ₜ l) =
      algebraMap L (FiniteAdeleRing B L) l := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := B) l
  have hy0 : algebraMap B L y ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hy (IsFractionRing.injective B L (by rw [h, map_zero]))
  have hl : l * algebraMap B L y = algebraMap B L x := by
    rw [← hxy, div_mul_cancel₀ _ hy0]
  have ht : ((1 : FiniteAdeleRing A K) ⊗ₜ[K] l) * (1 ⊗ₜ (algebraMap B L y)) =
      (1 : FiniteAdeleRing A K) ⊗ₜ (algebraMap B L x) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hl]
  have happ := congrArg (finiteBaseChangeRingEquiv A K L B) ht
  rw [map_mul, finiteBaseChangeRingEquiv_one_tmul_algebraMap,
    finiteBaseChangeRingEquiv_one_tmul_algebraMap] at happ
  have hr : algebraMap L (FiniteAdeleRing B L) l *
      algebraMap L (FiniteAdeleRing B L) (algebraMap B L y) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap B L x) := by
    rw [← map_mul, hl]
  have hu : IsUnit (algebraMap L (FiniteAdeleRing B L) (algebraMap B L y)) :=
    (IsUnit.mk0 _ hy0).map (algebraMap L (FiniteAdeleRing B L))
  exact hu.mul_right_cancel (happ.trans hr.symm)

def finiteTensorEquiv :
    letI := (finiteConorm A K L B).toAlgebra
    ((FiniteAdeleRing A K) ⊗[K] L) ≃ₐ[FiniteAdeleRing A K] (FiniteAdeleRing B L) :=
  letI := (finiteConorm A K L B).toAlgebra
  AlgEquiv.ofRingEquiv (f := finiteBaseChangeRingEquiv A K L B) (fun x => by
    rw [show algebraMap (FiniteAdeleRing A K) ((FiniteAdeleRing A K) ⊗[K] L) x = x ⊗ₜ 1 from rfl]
    rw [finiteBaseChangeRingEquiv_tmul_one]
    rfl)

theorem finiteTensorEquiv_apply (z : (FiniteAdeleRing A K) ⊗[K] L) :
    finiteTensorEquiv A K L B z = finiteBaseChangeRingEquiv A K L B z := rfl

theorem finiteTensorEquiv_one_tmul (l : L) :
    finiteTensorEquiv A K L B ((1 : FiniteAdeleRing A K) ⊗ₜ l) = algebraMap L (FiniteAdeleRing B L) l :=
  finiteBaseChangeRingEquiv_one_tmul A K L B l

theorem finiteTensorEquiv_tmul_one (x : FiniteAdeleRing A K) :
    finiteTensorEquiv A K L B (x ⊗ₜ (1 : L)) = finiteConorm A K L B x :=
  finiteBaseChangeRingEquiv_tmul_one A K L B x

end AKLB

end M4aHerbrand.Bridge

end
