import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma algHom_toLinearMap_span_top_of_finrank_le (K B : Type*) [Field K] [Ring B] [Algebra K B] [Module.Finite K B] (h : Module.finrank K B ≤ Nat.card (B →ₐ[K] K)) : Submodule.span K (Set.range (AlgHom.toLinearMap : (B →ₐ[K] K) → B →ₗ[K] K)) = ⊤ := by
  classical
  have hli : LinearIndependent K (AlgHom.toLinearMap : (B →ₐ[K] K) → B →ₗ[K] K) :=
    linearIndependent_algHom_toLinearMap K B K
  obtain hemp | _ := isEmpty_or_nonempty (B →ₐ[K] K)
  ·
    rw [Nat.card_of_isEmpty, Nat.le_zero] at h
    have hdtriv : Module.finrank K (B →ₗ[K] K) = 0 := by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one, h]
    let _ := Module.finrank_zero_iff.mp hdtriv
    apply Subsingleton.elim _ _
  let _ : Finite (B →ₐ[K] K) := hli.finite
  let _ : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  have hrk : Module.finrank K (B →ₗ[K] K) = Module.finrank K B := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  have hcardeq : Nat.card (B →ₐ[K] K) = Fintype.card (B →ₐ[K] K) :=
    Nat.card_eq_fintype_card (α := B →ₐ[K] K)
  have hcard : Fintype.card (B →ₐ[K] K) = Module.finrank K (B →ₗ[K] K) := by
    apply le_antisymm
    ·
      have hD := card_algHom_le_finrank K B K
      rw [hrk]
      simpa [Nat.card_eq_fintype_card] using hD
    ·
      rw [hrk, ← hcardeq]
      apply h
  refine hli.span_eq_top_of_card_eq_finrank' hcard
private lemma isReduced_of_finrank_le (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B] (h : Module.finrank K B ≤ Nat.card (B →ₐ[K] K)) : IsReduced B := by
  constructor
  intro b ⟨n, hbn⟩
  have hspan := algHom_toLinearMap_span_top_of_finrank_le K B h
  have hvan : ∀ ℓ : B →ₗ[K] K, ℓ b = 0 := by
    intro ℓ
    have hℓmem : ℓ ∈ (⊤ : Submodule K (B →ₗ[K] K)) := trivial
    rw [← hspan] at hℓmem
    induction hℓmem using Submodule.span_induction
    ·
      rename_i x hx
      obtain ⟨φ, rfl⟩ := hx
      show φ b = 0
      apply IsNilpotent.eq_zero ⟨n, by rw [← map_pow, hbn, map_zero]⟩
    ·
      simp
    ·
      rename_i x y _ _ hx hy
      simp [hx, hy]
    ·
      rename_i c x _ hx
      simp [hx]
  have heval : Module.Dual.eval K B b = 0 :=
    LinearMap.ext fun ℓ => by simp [Module.Dual.eval_apply, hvan ℓ]
  have hinj := (Module.evalEquiv K B).injective
  have : Module.evalEquiv K B b = Module.evalEquiv K B 0 := by
    rw [map_zero]; exact_mod_cast heval
  apply hinj this
/--
[IsReduced_of_finrank_le_natCard_algHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsReduced_of_finrank_le_natCard_algHom.lean)
-/
@[path]
private lemma main
  (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B]
  (h : Module.finrank K B ≤ Nat.card (B →ₐ[K] K)) :
  -- imply
  IsReduced B :=
  isReduced_of_finrank_le K B h


-- created on 2026-10-20
