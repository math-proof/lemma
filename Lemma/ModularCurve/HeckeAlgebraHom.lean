import Lemma.Gamma0HeckeOperatorHom.Main
import Lemma.ModularCurve.PeriodMap
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Finiteness
import Def.ModularCurve_HeckeAlgebraHom

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve.Period

section FGInfrastructure


theorem evalGen_injective {S : Set G} (hS : Subgroup.closure S = ⊤) :
    Function.Injective (evalGen S) := by
  intro φ ψ h
  refine AddMonoidHom.ext fun γ => ?_
  have hmem : Additive.toMul γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top _
  suffices hkey : φ (Additive.ofMul (Additive.toMul γ)) = ψ (Additive.ofMul (Additive.toMul γ)) by
    simpa using hkey
  set g := Additive.toMul γ
  clear_value g; clear γ
  induction hmem using Subgroup.closure_induction with
  | mem s hs => exact congrFun h ⟨s, hs⟩
  | one => simp
  | mul a b _ _ iha ihb =>
      have hmul : (Additive.ofMul (a * b) : Additive G) = Additive.ofMul a + Additive.ofMul b := rfl
      rw [hmul, map_add, map_add, iha, ihb]
  | inv a _ iha =>
      have hinv : (Additive.ofMul a⁻¹ : Additive G) = -Additive.ofMul a := rfl
      rw [hinv, map_neg, map_neg, iha]

theorem addHom_int_moduleFinite [Group.FG G] : Module.Finite ℤ (Additive G →+ ℤ) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  haveI : Finite S := hSfin
  exact Module.Finite.of_injective (evalGen S) (evalGen_injective hS)


theorem moduleEnd_addHom_int_moduleFinite [Group.FG G] :
    Module.Finite ℤ (Module.End ℤ (Additive G →+ ℤ)) := by
  haveI := addHom_int_moduleFinite (G := G)
  set M := Additive G →+ ℤ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := M)
  let ev : Module.End ℤ M →ₗ[ℤ] (s → M) :=
    { toFun := fun f i => f (i : M)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective ev ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro f hf
  simp only [Submodule.mem_bot, LinearMap.mem_ker] at hf ⊢
  refine LinearMap.ext fun m => ?_
  have hm : m ∈ (⊤ : Submodule ℤ M) := Submodule.mem_top
  rw [← hs] at hm
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
  · intro x hx
    exact congrFun hf ⟨x, hx⟩
  · simp
  · intro x y _ _ ihx ihy
    simp [map_add, ihx, ihy]
  · intro c x _ ihx
    simp [map_smul, ihx]

end FGInfrastructure

end ModularCurve.Period
