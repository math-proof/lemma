/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KrasnerLemma
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import sympy.atlas.v1.Atlas.NumberTheoryI.code.KrasnerLemma
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import sympy.atlas.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

def algEquivOfFinrankOne (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E = 1) : E ≃ₐ[F] F := by
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hsurj : Function.Surjective (algebraMap F E) := fun x => by
    have : x ∈ (⊤ : Subalgebra F E) := Algebra.mem_top; rwa [← htop] at this
  exact (AlgEquiv.ofBijective (Algebra.ofId F E) ⟨(algebraMap F E).injective, hsurj⟩).symm

lemma algEquiv_eq_refl_of_finrank_one {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E = 1) (e : E ≃ₐ[F] E) :
    e = AlgEquiv.refl := by
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h
  ext x
  have hx : x ∈ (⊤ : Subalgebra F E) := Algebra.mem_top
  rw [← htop] at hx
  obtain ⟨y, rfl⟩ := hx
  simp [AlgEquiv.commutes]

def galoisGroupMulEquivTrivial (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] (h : Module.finrank F E = 1) :
    MulEquiv (K ≃ₐ[K] K) (E ≃ₐ[F] E) where
  toFun _ := AlgEquiv.refl
  invFun _ := AlgEquiv.refl
  left_inv e := by ext x; exact (AlgEquiv.commutes e x).symm
  right_inv e := (algEquiv_eq_refl_of_finrank_one h e).symm
  map_mul' _ _ := by symm; exact algEquiv_eq_refl_of_finrank_one h _

noncomputable def commKvAlgEquiv (v : HeightOneSpectrum (𝓞 K)) :
    letI := @Algebra.TensorProduct.rightAlgebra K L (v.adicCompletion K) _ _ _ _ _
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K) := by
  letI := @Algebra.TensorProduct.rightAlgebra K L (v.adicCompletion K) _ _ _ _ _
  exact @AlgEquiv.ofRingEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    inferInstance
    Algebra.TensorProduct.rightAlgebra
    (f := (Algebra.TensorProduct.comm K (v.adicCompletion K) L).toRingEquiv)
    (fun r => by
      simp [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.right_algebraMap_apply])

lemma norm_baseChange_eq
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
    @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.norm_apply K α, ← LinearMap.det_baseChange (Algebra.lmul K L α),
      Algebra.baseChange_lmul, ← Algebra.norm_apply (v.adicCompletion K)
        ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : commKvAlgEquiv v ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
    simp [commKvAlgEquiv, AlgEquiv.ofRingEquiv, Algebra.TensorProduct.comm_tmul]
  rw [← h]
  exact (@Algebra.norm_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra (commKvAlgEquiv v)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

lemma trace_baseChange_eq
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
    @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.trace_apply K α,
      ← LinearMap.trace_baseChange (Algebra.lmul K L α) (v.adicCompletion K),
      Algebra.baseChange_lmul,
      ← Algebra.trace_apply (v.adicCompletion K) ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : commKvAlgEquiv v ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
    simp [commKvAlgEquiv, AlgEquiv.ofRingEquiv, Algebra.TensorProduct.comm_tmul]
  rw [← h]
  exact (@Algebra.trace_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra (commKvAlgEquiv v)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

def finSuccLinearEquiv' (R : Type*) [CommRing R] {n : ℕ} (A : Fin (n + 1) → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    (∀ i : Fin (n + 1), A i) ≃ₗ[R] A 0 × (∀ i : Fin n, A (Fin.succ i)) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by ext i; exact congr_fun (Fin.cons_self_tail f) i
  right_inv p := by
    ext
    · exact Fin.cons_zero p.1 p.2
    · exact Fin.cons_succ p.1 p.2 _
  map_add' f g := by ext <;> rfl
  map_smul' r f := by ext <;> rfl

lemma norm_pi_fin' {R : Type*} [CommRing R]
    {n : ℕ} {A : Fin n → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    Algebra.norm R f = ∏ i, Algebra.norm R (f i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact (congr_arg _ (Subsingleton.elim f 1)).trans (map_one _)
  | succ n ih =>
    let e := finSuccLinearEquiv' R A
    have step1 : Algebra.norm R f =
        LinearMap.det (e.toLinearMap ∘ₗ (Algebra.lmul R _ f) ∘ₗ e.symm.toLinearMap) := by
      rw [LinearMap.det_conj, Algebra.norm_apply]
    have hmul : e.toLinearMap ∘ₗ (Algebra.lmul R _ f) ∘ₗ e.symm.toLinearMap =
        ((Algebra.lmul R (A 0)) (f 0)).prodMap ((Algebra.lmul R _) (Fin.tail f)) := by
      apply LinearMap.ext; intro ⟨a, g⟩
      show e (f * e.symm (a, g)) = (f 0 * a, Fin.tail f * g)
      simp only [e, finSuccLinearEquiv', LinearEquiv.coe_mk]
      ext
      · simp [Pi.mul_apply, Fin.cons_zero]
      · simp [Pi.mul_apply, Fin.tail, Fin.cons_succ]
    rw [step1, hmul, LinearMap.det_prodMap, ← Algebra.norm_apply, ← Algebra.norm_apply,
        ih (Fin.tail f), Fin.prod_univ_succ]
    simp only [Fin.tail]

theorem Algebra.norm_pi_apply' {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    (Algebra.norm R) f = ∏ i, (Algebra.norm R) (f i) := by
  classical
  let e := Fintype.equivFin ι
  let φ := AlgEquiv.piCongrLeft R A e.symm
  have h1 : Algebra.norm R f = Algebra.norm R (φ.symm f) := by
    conv_lhs => rw [← φ.apply_symm_apply f]
    exact Algebra.norm_eq_of_algEquiv φ (φ.symm f)
  rw [h1, norm_pi_fin' (φ.symm f)]
  exact Fintype.prod_equiv e.symm _ _ (fun j => by congr 1)

lemma algEquiv_tmul_one_component
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L))
    (e : @AlgEquiv (v.adicCompletion K)
      (L ⊗[K] v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L)
      _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _))
    (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α)
    (α : L)
    (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) :
    e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α :=
  he α w

lemma norm_pi_eq_prod
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L))
    (e : @AlgEquiv (v.adicCompletion K)
      (L ⊗[K] v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L)
      _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _))
    (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α)
    (α : L) :
    @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) =
    ∏ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Algebra.norm (v.adicCompletion K) (w.val.adicCompletion L) _ _ (localAlg w)
        (algebraMap L (w.val.adicCompletion L) α) := by
  classical


  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w =>
    @Module.Free.of_divisionRing (v.adicCompletion K) (w.val.adicCompletion L)
      inferInstance inferInstance (localAlg w).toModule
  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Finite (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w => by
    letI := localAlg w

    letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite (v.adicCompletion K)
        (v.adicCompletion K ⊗[K] L) := Module.Finite.base_change K _ L
    haveI : Module.Finite (v.adicCompletion K)
        ((w' : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
          w'.val.adicCompletion L) :=
      Module.Finite.equiv ((commKvAlgEquiv v).trans e).toLinearEquiv
    exact Module.Finite.of_surjective
      (@LinearMap.proj (v.adicCompletion K) _ _
        (fun w' => w'.val.adicCompletion L) _ (fun w' => (localAlg w').toModule) w)
      (LinearMap.proj_surjective w)


  letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
    Algebra.TensorProduct.rightAlgebra
  rw [← Algebra.norm_eq_of_algEquiv e (α ⊗ₜ[K] 1)]

  rw [Algebra.norm_pi_apply' (e (α ⊗ₜ[K] 1))]

  congr 1; ext w; congr 1
  exact algEquiv_tmul_one_component v localAlg e he α w

lemma trace_single_comp_aux {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (j : ι) (f : A j →ₗ[R] A j) :
    (LinearMap.trace R (∀ i, A i)) ((LinearMap.single R A j) ∘ₗ (f ∘ₗ (LinearMap.proj j))) =
    (LinearMap.trace R (A j)) f := by
  rw [LinearMap.trace_comp_comm' (f ∘ₗ LinearMap.proj j) (LinearMap.single R A j)]
  congr 1; ext x
  simp [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]

lemma pi_lmul_decomp_aux {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (f : ∀ i, A i) :
    (Algebra.lmul R (∀ i, A i) f) =
    ∑ i : ι, (LinearMap.single R A i).comp
      ((Algebra.lmul R (A i) (f i)).comp (LinearMap.proj i)) := by
  apply LinearMap.ext; intro x; funext k
  simp only [LinearMap.comp_apply, LinearMap.proj_apply,
             LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single k (fun b _ hbk => ?_) (fun hk => ?_)]
  · simp [LinearMap.single_apply]
  · simp [LinearMap.single_apply, hbk]
  · exact absurd (Finset.mem_univ k) hk

theorem Algebra.trace_pi_apply' {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    (Algebra.trace R (∀ i, A i)) f = ∑ i, (Algebra.trace R (A i)) (f i) := by
  simp only [Algebra.trace_apply]
  rw [pi_lmul_decomp_aux f, map_sum]
  congr 1; ext i; exact trace_single_comp_aux i _

lemma trace_pi_eq_sum
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L))
    (e : @AlgEquiv (v.adicCompletion K)
      (L ⊗[K] v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L)
      _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _))
    (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α)
    (α : L) :
    @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) =
    ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L) _ _ (localAlg w)
        (algebraMap L (w.val.adicCompletion L) α) := by
  classical

  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w =>
    @Module.Free.of_divisionRing (v.adicCompletion K) (w.val.adicCompletion L)
      inferInstance inferInstance (localAlg w).toModule
  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Finite (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w => by
    letI := localAlg w

    letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite (v.adicCompletion K)
        (v.adicCompletion K ⊗[K] L) := Module.Finite.base_change K _ L
    haveI : Module.Finite (v.adicCompletion K)
        ((w' : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
          w'.val.adicCompletion L) :=
      Module.Finite.equiv ((commKvAlgEquiv v).trans e).toLinearEquiv
    exact Module.Finite.of_surjective
      (@LinearMap.proj (v.adicCompletion K) _ _
        (fun w' => w'.val.adicCompletion L) _ (fun w' => (localAlg w').toModule) w)
      (LinearMap.proj_surjective w)


  letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
    Algebra.TensorProduct.rightAlgebra
  rw [← Algebra.trace_eq_of_algEquiv e (α ⊗ₜ[K] 1)]

  rw [Algebra.trace_pi_apply' (e (α ⊗ₜ[K] 1))]

  congr 1; ext w; congr 1
  exact algEquiv_tmul_one_component v localAlg e he α w

theorem norm_eq_prod_localNorm
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
    ∏ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Algebra.norm (v.adicCompletion K) (w.val.adicCompletion L) _ _
        ((completionEmbedding_finite v w.val w.prop).toAlgebra)
        (algebraMap L (w.val.adicCompletion L) α) := by

  rw [norm_baseChange_eq v α]


  obtain ⟨e, he⟩ := theorem_13_5_finite_place_Kv (L := L) v

  exact norm_pi_eq_prod v
    (fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra) e he α

theorem trace_eq_sum_localTrace
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
    ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L) _ _
        ((completionEmbedding_finite v w.val w.prop).toAlgebra)
        (algebraMap L (w.val.adicCompletion L) α) := by

  rw [trace_baseChange_eq v α]


  obtain ⟨e, he⟩ := theorem_13_5_finite_place_Kv (L := L) v

  exact trace_pi_eq_sum v
    (fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra) e he α

theorem norm_trace_completion_decomposition
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (α : L) :
    (algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
      ∏ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
        @Algebra.norm (v.adicCompletion K) (w.val.adicCompletion L) _ _
          ((completionEmbedding_finite v w.val w.prop).toAlgebra)
          (algebraMap L (w.val.adicCompletion L) α))
    ∧
    (algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
      ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
        @Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L) _ _
          ((completionEmbedding_finite v w.val w.prop).toAlgebra)
          (algebraMap L (w.val.adicCompletion L) α)) :=
  ⟨norm_eq_prod_localNorm v α, trace_eq_sum_localTrace v α⟩

end NormTraceCompletion

section NormTraceCompletionAliases

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

abbrev corollary_11_24 := @norm_trace_completion_decomposition K L _ _ _ _ _

end NormTraceCompletionAliases

end
