import Mathlib
import sympy.Basic
open scoped TensorProduct


private lemma exists_map_eq_of_coeffs_subset
  {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  {n : ℕ} {L : IntermediateField k K} {p : MvPolynomial (Fin n) K}
-- given
  (hp : (↑p.coeffs : Set K) ⊆ (L : Set K)) :
-- imply
  ∃ q : MvPolynomial (Fin n) L, MvPolynomial.map (algebraMap L K) q = p := by
-- proof
  have : p ∈ Set.range (MvPolynomial.map (algebraMap L K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    refine ⟨⟨c, hp hc⟩, rfl⟩
  apply this

private lemma exists_model_of_lifts
  {L₀ K : Type v} [CommRing L₀] [CommRing K] [Algebra L₀ K]
  {A : Type w} [CommRing A] [Algebra K A] [Algebra L₀ A] [IsScalarTower L₀ K A]
  {n : ℕ} {f : MvPolynomial (Fin n) K →ₐ[K] A}
  {s : Finset (MvPolynomial (Fin n) K)}
  {q : ∀ p ∈ s, MvPolynomial (Fin n) L₀}
-- given
  (hf : Function.Surjective f)
  (hs : Ideal.span (↑s : Set (MvPolynomial (Fin n) K)) = RingHom.ker f)
  (hq : ∀ p (hp : p ∈ s), MvPolynomial.map (algebraMap L₀ K) (q p hp) = p) :
-- imply
  ∃ (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra L₀ A₀) (_ : Algebra.FiniteType L₀ A₀),
    Nonempty ((K ⊗[L₀] A₀) ≃ₐ[K] A) := by
-- proof
  classical
  let I : Ideal (MvPolynomial (Fin n) L₀) := Ideal.span (Set.range fun p : s => q p.1 p.2)
  let A₀ : Type v := MvPolynomial (Fin n) L₀ ⧸ I
  let φ₀ : MvPolynomial (Fin n) L₀ →ₐ[L₀] A := MvPolynomial.aeval fun i => f (MvPolynomial.X i)
  have hfae : ∀ p : MvPolynomial (Fin n) K, f p = MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) p :=
    fun p => by
      have hf' : f = MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) :=
        MvPolynomial.algHom_ext (fun i => by simp)
      conv_lhs => rw [hf']
  have hφ₀ : ∀ p : MvPolynomial (Fin n) L₀, φ₀ p = f (MvPolynomial.map (algebraMap L₀ K) p) := fun p => by
    rw [hfae, MvPolynomial.aeval_map_algebraMap]
  have hφ₀I : ∀ a ∈ I, φ₀ a = 0 := by
    have hle : I ≤ RingHom.ker (φ₀ : MvPolynomial (Fin n) L₀ →+* A) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨⟨p, hp⟩, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show φ₀ (q p hp) = 0
      rw [hφ₀, hq p hp]
      apply RingHom.mem_ker.mp (hs ▸ Ideal.subset_span hp)
    intro a ha
    apply hle ha
  let g : A₀ →ₐ[L₀] A := Ideal.Quotient.liftₐ I φ₀ hφ₀I
  let Φ : K ⊗[L₀] A₀ →ₐ[K] A := AlgHom.liftEquiv L₀ K A₀ A g
  let ψ₀ : MvPolynomial (Fin n) K →ₐ[K] K ⊗[L₀] A₀ :=
    MvPolynomial.aeval fun i => (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (MvPolynomial.X i) : A₀)
  have hψ₀map : ∀ p : MvPolynomial (Fin n) L₀,
      ψ₀ (MvPolynomial.map (algebraMap L₀ K) p) = (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I p : A₀) := fun p => by
    change (MvPolynomial.aeval fun i => (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (MvPolynomial.X i) : A₀))
      (MvPolynomial.map (algebraMap L₀ K) p) = _
    rw [MvPolynomial.aeval_map_algebraMap]
    have : (MvPolynomial.aeval (R := L₀) (S₁ := K ⊗[L₀] A₀)
          fun i => (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (MvPolynomial.X i) : A₀)) =
        ((Algebra.TensorProduct.includeRight (R := L₀) (A := K) (B := A₀)).comp
          (Ideal.Quotient.mkₐ L₀ I)) :=
      MvPolynomial.algHom_ext fun i => by
        rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
        rfl
    rw [this]
    rfl
  have hψ₀J : ∀ a ∈ RingHom.ker f, ψ₀ a = 0 := by
    have hle : RingHom.ker f ≤
        RingHom.ker (ψ₀ : MvPolynomial (Fin n) K →ₐ[K] K ⊗[L₀] A₀).toRingHom := by
      rw [← hs]
      refine Ideal.span_le.mpr fun p hp => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show ψ₀ p = 0
      rw [← hq p hp, hψ₀map]
      have : (Ideal.Quotient.mk I (q p hp) : A₀) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨⟨p, hp⟩, rfl⟩)
      rw [this, TensorProduct.tmul_zero]
    intro a ha
    apply hle ha
  let e : (MvPolynomial (Fin n) K ⧸ RingHom.ker f) ≃ₐ[K] A := Ideal.quotientKerAlgEquivOfSurjective hf
  let Ψ : A →ₐ[K] K ⊗[L₀] A₀ :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) ψ₀ hψ₀J).comp (e.symm : A →ₐ[K] _)
  have hΦ : ∀ p : MvPolynomial (Fin n) L₀,
      Φ ((1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I p : A₀)) = f (MvPolynomial.map (algebraMap L₀ K) p) := by
    intro p
    change (AlgHom.liftEquiv L₀ K A₀ A g) ((1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I p : A₀)) = _
    rw [AlgHom.liftEquiv_tmul, one_smul]
    have hcomp := Ideal.Quotient.liftₐ_comp (R₁ := L₀) I φ₀ hφ₀I
    have hp := DFunLike.congr_fun hcomp p
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hp
    rw [hp]
    apply hφ₀
  have hΨ : ∀ p : MvPolynomial (Fin n) K, Ψ (f p) = ψ₀ p := by
    intro p
    change Ideal.Quotient.liftₐ (RingHom.ker f) ψ₀ hψ₀J (e.symm (f p)) = ψ₀ p
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply hf p]
    have hcomp := Ideal.Quotient.liftₐ_comp (R₁ := K) (RingHom.ker f) ψ₀ hψ₀J
    have hp := DFunLike.congr_fun hcomp p
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hp
    apply hp
  have h₁ : Φ.comp Ψ = AlgHom.id K A := by
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hf a
    rw [AlgHom.comp_apply, hΨ, AlgHom.id_apply]
    have : Φ.comp ψ₀ = f := MvPolynomial.algHom_ext fun i => by
      rw [AlgHom.comp_apply]
      change Φ (MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[L₀]
        (Ideal.Quotient.mk I (MvPolynomial.X i) : A₀)) (MvPolynomial.X i)) = f (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X, hΦ, MvPolynomial.map_X]
    apply AlgHom.congr_fun this p
  have h₂ : Ψ.comp Φ = AlgHom.id K (K ⊗[L₀] A₀) := by
    apply Algebra.TensorProduct.ext
    · apply Subsingleton.elim
    ·
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      change Ψ (Φ ((1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (MvPolynomial.X i) : A₀))) =
        (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (MvPolynomial.X i) : A₀)
      rw [hΦ, hΨ, hψ₀map]
  let _ : Algebra.FiniteType L₀ A₀ := inferInstance
  refine ⟨A₀, inferInstance, inferInstance, inferInstance, ⟨AlgEquiv.ofAlgHom Φ Ψ h₁ h₂⟩⟩


/--
[Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic.lean)
-/
@[path]
private lemma main
  {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  {A : Type w} [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
-- imply
  ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra L A₀) (_ : Algebra.FiniteType L A₀),
    Nonempty ((K ⊗[L] A₀) ≃ₐ[K] A) := by
-- proof
  classical
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := K) (S := A)).mp inferInstance
  obtain ⟨s, hs⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _
  let C : Finset K := s.biUnion fun p => p.coeffs
  let L : IntermediateField k K := IntermediateField.adjoin k (↑C : Set K)
  have hLfd : FiniteDimensional k L := by
    let _ : Finite (↑(↑C : Set K)) := Finite.of_fintype _
    apply IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral
  have hlift : ∀ p ∈ s, ∃ q : MvPolynomial (Fin n) L, MvPolynomial.map (algebraMap L K) q = p := by
    intro p hp
    refine exists_map_eq_of_coeffs_subset (L := L) (p := p) fun c hc => ?_
    apply IntermediateField.subset_adjoin k _ (Finset.mem_biUnion.mpr ⟨p, hp, hc⟩)
  choose q hq using hlift
  refine ⟨L, hLfd, exists_model_of_lifts (L₀ := L) (f := f) (s := s) (q := q) hf hs hq⟩


-- created on 2026-10-13
