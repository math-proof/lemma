import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[IntermediateField_exists_finiteDimensional_le_forall_mem_of_algEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_exists_finiteDimensional_le_forall_mem_of_algEquiv.lean)
-/
@[path]
private lemma main
    {F E : Type} [Field F] [Field E] [Algebra F E] (halg : Algebra.IsAlgebraic F E)
    (k₀ : IntermediateField F E) (τ : E ≃ₐ[F] E) (hk₀ : ∀ x : E, x ∈ k₀ → τ x ∈ k₀)
    (K : IntermediateField ↥k₀ E) (hK : FiniteDimensional ↥k₀ ↥K) :
    ∃ K' : IntermediateField ↥k₀ E, FiniteDimensional ↥k₀ ↥K' ∧ K ≤ K' ∧ ∀ x : E, x ∈ K' → τ x ∈ K' := by
  classical
  let _ := halg
  let _ := hK
  let b := Module.finBasis (↥k₀) (↥K)
  let T : Set E := ⋃ i, (minpoly F ((b i : ↥K) : E)).rootSet E
  have hTfin : T.Finite := Set.finite_iUnion (fun i => Polynomial.rootSet_finite _ _)
  let _ : Finite ↥T := hTfin.to_subtype
  have hint : ∀ i, IsIntegral F ((b i : ↥K) : E) := fun i => (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hbT : ∀ i, ((b i : ↥K) : E) ∈ T := by
    intro i
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero (hint i), minpoly.aeval F _⟩
  have hTτ : ∀ x ∈ T, τ x ∈ T := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [Polynomial.mem_rootSet] at hi ⊢
    refine ⟨hi.1, ?_⟩
    rw [Polynomial.aeval_algHom_apply τ x, hi.2, map_zero]
  have hTint : ∀ x ∈ T, IsIntegral (↥k₀) x := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [Polynomial.mem_rootSet] at hi
    have hF : IsIntegral F x := ⟨minpoly F ((b i : ↥K) : E), minpoly.monic (hint i), hi.2⟩
    exact hF.tower_top
  let K' : IntermediateField (↥k₀) E := IntermediateField.adjoin (↥k₀) T
  refine ⟨K', IntermediateField.finiteDimensional_adjoin hTint, ?_, ?_⟩
  ·
    intro x hx
    have hrepr := b.sum_repr ⟨x, hx⟩
    have hxE : x = ∑ i, ((b.repr ⟨x, hx⟩ i : ↥k₀) : E) * ((b i : ↥K) : E) := by
      have h1 : ((⟨x, hx⟩ : ↥K) : E) = ((∑ i, b.repr ⟨x, hx⟩ i • b i : ↥K) : E) :=
        congrArg (fun z : ↥K => (z : E)) hrepr.symm
      calc x = ((⟨x, hx⟩ : ↥K) : E) := rfl
        _ = ((∑ i, b.repr ⟨x, hx⟩ i • b i : ↥K) : E) := h1
        _ = ∑ i, ((b.repr ⟨x, hx⟩ i : ↥k₀) : E) * ((b i : ↥K) : E) := by
          push_cast
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Algebra.smul_def]
          push_cast
          rfl
    rw [hxE]
    refine K'.sum_mem (fun i _ => K'.mul_mem ?_ ?_)
    · exact K'.algebraMap_mem _
    · exact IntermediateField.subset_adjoin _ _ (hbT i)
  ·
    let K'' : IntermediateField (↥k₀) E :=
      (K'.toSubfield.comap τ.toRingEquiv.toRingHom).toIntermediateField (fun c => by
        show τ (algebraMap (↥k₀) E c) ∈ K'
        exact K'.toSubalgebra.algebraMap_mem' ⟨τ (c : E), hk₀ _ c.2⟩ |> fun h => by simpa using h)
    have hle : K' ≤ K'' := by
      change IntermediateField.adjoin (↥k₀) T ≤ K''
      rw [IntermediateField.adjoin_le_iff]
      intro t ht
      show τ t ∈ K'
      exact IntermediateField.subset_adjoin _ _ (hTτ t ht)
    intro x hx
    exact hle hx

-- created on 2026-10-20
