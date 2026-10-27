import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma span_mkQ_tmul_eq_top {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {ι : Type} (g : ι → M) {K : Type} [Field K] [Algebra R K] (hg : Submodule.span R (Set.range g) = ⊤) (N : Submodule K (K ⊗[R] M)) : Submodule.span K (Set.range fun t => N.mkQ ((1 : K) ⊗ₜ[R] g t)) = ⊤ := by
  have h1 : Submodule.span K (Set.range fun t => (1 : K) ⊗ₜ[R] g t) = ⊤ := by
    have := Submodule.baseChange_span (R := R) (A := K) (M := M) (Set.range g)
    rw [hg, Submodule.baseChange_top] at this
    rw [this, ← Set.range_comp]
    rfl
  have h2 : Set.range (fun t => N.mkQ ((1 : K) ⊗ₜ[R] g t)) = N.mkQ '' Set.range fun t => (1 : K) ⊗ₜ[R] g t := by
    rw [← Set.range_comp]; rfl
  rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
private lemma finrank_quotient_eq {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} {K : Type} [Field K] [Algebra R K] (N : Module.Grassmannian K (K ⊗[R] M) k) : Module.finrank K ((K ⊗[R] M) ⧸ N.toSubmodule) = k := by
  have h := N.rankAtStalk_eq ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact_mod_cast h
private lemma cover {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} {ι : Type} (g : ι → M) {K : Type} [Field K] [Algebra R K] (hg : Submodule.span R (Set.range g) = ⊤) (N : Module.Grassmannian K (K ⊗[R] M) k) : ∃ I : Fin k → ι, Function.Injective I ∧ Function.Bijective (fun v : Fin k → K => ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i))) := by
  classical
  set w : ι → (K ⊗[R] M) ⧸ N.toSubmodule := fun t => N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g t) with hw
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K w
  rw [span_mkQ_tmul_eq_top g hg] at hsp
  let b : Module.Basis κ K ((K ⊗[R] M) ⧸ N.toSubmodule) := Module.Basis.mk hli (by rw [hsp])
  let _ : Finite κ := Module.Finite.finite_basis b
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← finrank_quotient_eq N, Module.finrank_eq_card_basis b]
  let e : κ ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin k) K ((K ⊗[R] M) ⧸ N.toSubmodule) := b.reindex e
  have hb' : ∀ i, b' i = w (a (e.symm i)) := fun i => by
    simp [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]
  refine ⟨fun i => a (e.symm i), ha.comp e.symm.injective, ?_⟩
  have hfun : (fun v : Fin k → K => ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (a (e.symm i)))) =
      b'.equivFun.symm := by
    funext v
    rw [Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl fun i _ => by rw [hb']
  rw [hfun]
  apply b'.equivFun.symm.bijective
/--
[Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top.lean)
-/
@[path]
private lemma main
  (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
  (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
  (K : Type) [Field K] [Algebra R K] (N : Module.Grassmannian K (K ⊗[R] M) k) :
  -- imply
  ∃ I : Fin k → ι, Function.Injective I ∧ Function.Bijective (fun v : Fin k → K => ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i))) :=
  cover g hg N


-- created on 2026-10-20
