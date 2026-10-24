import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot.lean)
-/
@[path]
private lemma main
  (B : Type u) [CommRing B] (M : Type v) [AddCommGroup M] [Module B M]
  [Module.Finite B M] [Module.Projective B M] (x : M) :
  -- imply
  ∃ J : Ideal B, J.FG ∧ ∀ (A : Type u) [CommRing A] [Algebra B A], ((1 : A) ⊗ₜ[B] x : A ⊗[B] M) = 0 ↔ Ideal.map (algebraMap B A) J = ⊥ := by
  -- proof
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := M)
  let p : (Fin n → B) →ₗ[B] M := Fintype.linearCombination B s
  have hp : Function.Surjective p := by
    intro m
    have hm : m ∈ Submodule.span B (Set.range s) := by rw [hs]; apply Submodule.mem_top
    rw [← Fintype.range_linearCombination B s] at hm
    apply hm
  obtain ⟨g, hg⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[B] M) hp
  refine ⟨Ideal.span (Set.range fun i : Fin n => g x i), Submodule.fg_span (Set.finite_range _), ?_⟩
  intro A _ _
  have hJ : Ideal.map (algebraMap B A) (Ideal.span (Set.range fun i : Fin n => g x i)) = ⊥ ↔ ∀ i, algebraMap B A (g x i) = 0 := by
    rw [Ideal.map_span, Ideal.span_eq_bot]
    constructor
    ·
      intro h i
      refine h _ ⟨g x i, ⟨i, rfl⟩, rfl⟩
    ·
      rintro h _ ⟨b, ⟨i, rfl⟩, rfl⟩
      apply h i
  rw [hJ]
  have hcoord : ∀ i : Fin n, (TensorProduct.rid B A) (LinearMap.lTensor A ((LinearMap.proj i).comp g) ((1 : A) ⊗ₜ[B] x)) = algebraMap B A (g x i) := by
    intro i
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, LinearMap.proj_apply, TensorProduct.rid_tmul]
    rw [Algebra.smul_def, mul_one]
  constructor
  ·
    intro h0 i
    have := hcoord i
    rw [h0, map_zero, map_zero] at this
    apply this.symm
  ·
    intro hzero
    have hx : x = p (g x) := by
      have := congrArg (fun f : M →ₗ[B] M => f x) hg
      simpa using this.symm
    have hgx : ((1 : A) ⊗ₜ[B] (g x) : A ⊗[B] (Fin n → B)) = 0 := by
      have hdecomp : g x = ∑ i : Fin n, (g x i) • (Pi.single i (1 : B) : Fin n → B) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hdecomp, TensorProduct.tmul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, hzero i, zero_mul, TensorProduct.zero_tmul]
    calc
      _ = LinearMap.lTensor A p ((1 : A) ⊗ₜ[B] (g x)) := by
        rw [LinearMap.lTensor_tmul, ← hx]
      _ = 0 := by rw [hgx, map_zero]


-- created on 2026-10-20
