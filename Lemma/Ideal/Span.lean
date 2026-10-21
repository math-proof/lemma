import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Ideal_isPrime_span_algebraMap_of_isDomain_tensor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_isPrime_span_algebraMap_of_isDomain_tensor.lean)
-/
@[path]
private lemma main
  [CommRing R]
  [CommRing A] [Algebra R A]
  [Field κ] [Algebra R κ]
  [IsDomain (TensorProduct R κ A)]
  (ϖ : R)
  -- given
  (hker : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ})
  (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal) :
  -- imply
  (Ideal.span {algebraMap R A ϖ} : Ideal A).IsPrime := by
  -- proof
  classical
  set I : Ideal R := Ideal.span {ϖ} with hI
  let _ : I.IsMaximal := hmax
  let _ : Field (R ⧸ I) := Ideal.Quotient.field I
  let qk : RingHom (R ⧸ I) κ :=
    Ideal.Quotient.lift I (algebraMap R κ) (fun r hr => by rwa [← RingHom.mem_ker, hker])
  let _ : Algebra (R ⧸ I) κ := qk.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) κ :=
    IsScalarTower.of_algebraMap_eq (fun r => (Ideal.Quotient.lift_mk I _ _).symm)
  let g : AlgHom R A (TensorProduct R κ A) := Algebra.TensorProduct.includeRight
  have hP : (RingHom.ker g).IsPrime := RingHom.ker_isPrime _
  suffices h : RingHom.ker g = Ideal.span {algebraMap R A ϖ} by
    rwa [← h]
  apply le_antisymm
  ·
    intro a ha
    rw [RingHom.mem_ker] at ha
    change TensorProduct.tmul R (1 : κ) a = 0 at ha
    let e1 : AlgEquiv A (A ⧸ I.map (algebraMap R A)) (TensorProduct R A (R ⧸ I)) :=
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I
    let e2 : AlgEquiv R (TensorProduct R A (R ⧸ I)) (TensorProduct R (R ⧸ I) A) :=
      Algebra.TensorProduct.comm R A (R ⧸ I)
    let j : AlgHom (R ⧸ I) (TensorProduct R (R ⧸ I) A)
      (TensorProduct (R ⧸ I) κ (TensorProduct R (R ⧸ I) A)) := Algebra.TensorProduct.includeRight
    let _ : Module.Free (R ⧸ I) (TensorProduct R (R ⧸ I) A) := Module.Free.of_divisionRing _ _
    have hj : Function.Injective j := Algebra.TensorProduct.includeRight_injective qk.injective
    let e3 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) κ κ A
    have hcomp : ∀ b : A, e3 (j (e2 (e1 (Ideal.Quotient.mk _ b)))) = TensorProduct.tmul R (1 : κ) b := by
      intro b
      have h1 : e1 (Ideal.Quotient.mk _ b) = TensorProduct.tmul R b (1 : R ⧸ I) :=
        Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk A I b
      rw [h1]
      change e3 (TensorProduct.tmul (R ⧸ I) (1 : κ) (Algebra.TensorProduct.comm R A (R ⧸ I) (TensorProduct.tmul R b (1 : R ⧸ I)))) = _
      rw [Algebra.TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have h0 : e3 (j (e2 (e1 (Ideal.Quotient.mk _ a)))) = 0 := by
      rw [hcomp, ha]
    rw [LinearEquiv.map_eq_zero_iff, ← map_zero j, hj.eq_iff, EmbeddingLike.map_eq_zero_iff,
      EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span, Set.image_singleton] at h0
    apply h0
  ·
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change TensorProduct.tmul R (1 : κ) (algebraMap R A ϖ) = 0
    have hϖ0 : algebraMap R κ ϖ = 0 := by
      rw [← RingHom.mem_ker, hker]
      apply Ideal.mem_span_singleton_self ϖ
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      mul_one, hϖ0, TensorProduct.zero_tmul]


-- created on 2026-10-20
