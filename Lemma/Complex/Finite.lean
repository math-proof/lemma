import Mathlib
import sympy.Basic

open CongruenceSubgroup
open scoped MatrixGroups

/--
[ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex.lean)
-/

private lemma  ModularCurve.Period.fg_gamma0 (N : ℕ) [NeZero N] : Group.FG (Gamma0 N) := by
  classical
  haveI : Group.FG SL(2, ℤ) := ⟨⟨{ModularGroup.S, ModularGroup.T}, by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact SpecialLinearGroup.SL2Z_generators⟩⟩
  exact Subgroup.fg_of_index_ne_zero _
@[main]
private lemma main
  {N : ℕ} [NeZero N] :
-- imply
  Module.Finite ℂ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℂ) := by
-- proof
  classical
  obtain ⟨s, hs⟩ := (ModularCurve.Period.fg_gamma0 N).out
  let ev : (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun φ i => φ (Additive.ofMul (i : Gamma0 N))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective ev ?_
  intro φ ψ h
  have key : ∀ γ : Gamma0 N, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (s : Set (Gamma0 N)) := by rw [hs]; exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx => exact congrFun h ⟨x, hx⟩
    | one => rw [ofMul_one, map_zero, map_zero]
    | mul x y _ _ hx hy => rw [ofMul_mul, map_add, map_add, hx, hy]
    | inv x _ hx => rw [ofMul_inv, map_neg, map_neg, hx]
  exact AddMonoidHom.ext fun a => key (Additive.toMul a)


-- created on 2026-10-05
