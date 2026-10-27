import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq.lean)
-/
@[path]
private lemma main
  {R : Type} [CommRing R]
  {k : Type} [CommRing k] [Algebra R k] [Nontrivial k]
  {G : Type} [Group G]
  {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  (hV : Module.finrank R V = 2)
  (ρV : G →* Module.End R V) (hspan : Submodule.span R (Set.range ⇑ρV) = ⊤) :
  -- imply
  Module.finrank k (k ⊗[R] V) = 2 ∧ Submodule.span k (Set.range (fun g : G => (ρV g).baseChange k)) = ⊤ ∧ (∀ g : G, LinearMap.trace k (k ⊗[R] V) ((ρV g).baseChange k) = algebraMap R k (LinearMap.trace R V (ρV g))) ∧ (∀ (g : G) (v : V), ((ρV g).baseChange k) ((1 : k) ⊗ₜ[R] v) = (1 : k) ⊗ₜ[R] (ρV g v)) ∧ (Function.Injective (algebraMap R k) → Function.Injective (fun v : V => (1 : k) ⊗ₜ[R] v)) := by
  -- proof
  classical
  let _ : Nontrivial R := by
    obtain h | h := subsingleton_or_nontrivial R
    ·
      exfalso
      have : Module.finrank R V = 1 := by simp [Module.finrank]
      omega
    ·
      apply h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Module.finrank_baseChange, hV]
  ·
    let b : Module.Basis (Fin 2) R V := Module.finBasisOfFinrankEq R V hV
    let bk := Algebra.TensorProduct.basis k b
    set S : Submodule k (Module.End k (k ⊗[R] V)) :=
      Submodule.span k (Set.range (fun g : G => (ρV g).baseChange k)) with hS
    have hmem : ∀ f : Module.End R V, f.baseChange k ∈ S := by
      intro f
      have hf : f ∈ Submodule.span R (Set.range ⇑ρV) := by rw [hspan]; trivial
      induction hf using Submodule.span_induction
      ·
        rename_i x hx
        obtain ⟨g, rfl⟩ := hx
        refine Submodule.subset_span ⟨g, rfl⟩
      ·
        rw [LinearMap.baseChange_zero]
        apply S.zero_mem
      ·
        rename_i x y _ _ hx hy
        rw [LinearMap.baseChange_add]
        apply S.add_mem hx hy
      ·
        rename_i r x _ hx
        rw [LinearMap.baseChange_smul]
        apply S.smul_of_tower_mem r hx
    apply top_unique
    rw [← (Module.Basis.end bk).span_eq, Submodule.span_le]
    rintro _ ⟨ij, rfl⟩
    rw [← Module.Basis.baseChange_end]
    apply hmem _
  ·
    intro g
    apply LinearMap.trace_baseChange (ρV g) k
  ·
    intro g v
    rfl
  ·
    intro hinj
    have h1 : Function.Injective ((Algebra.linearMap R k).rTensor V) :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := V) (Algebra.linearMap R k) hinj
    have h2 : Function.Injective (TensorProduct.lid R V).symm := (TensorProduct.lid R V).symm.injective
    have h3 : (fun v : V => (1 : k) ⊗ₜ[R] v) = ((Algebra.linearMap R k).rTensor V) ∘ (TensorProduct.lid R V).symm := by
      funext v
      simp [LinearMap.rTensor_tmul]
    rw [h3]
    apply h1.comp h2


-- created on 2026-10-20
