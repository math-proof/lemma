import Mathlib

set_option autoImplicit false

namespace AutomorphicForm

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop where
  isInternal : DirectSum.IsInternal wt
  map_raise_le : ∀ n : ℤ, (wt n).map E ≤ wt (n + 2)
  map_lower_le : ∀ n : ℤ, (wt n).map L ≤ wt (n - 2)
  raise_lower_sub : ∀ (n : ℤ) (v : M), v ∈ wt n → E (L v) - L (E v) = (n : ℂ) • v
  map_refl_le : ∀ n : ℤ, (wt n).map ε ≤ wt (-n)
  refl_comp_refl : ε ∘ₗ ε = LinearMap.id
  refl_comp_raise : ε ∘ₗ E = L ∘ₗ ε

def IsGL2RealKTypeSubmodule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (W : Submodule ℂ M) : Prop :=
  W ≤ (⨆ n : ℤ, W ⊓ wt n) ∧ W.map E ≤ W ∧ W.map L ≤ W ∧ W.map ε ≤ W

def IsIrreducibleGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop :=
  (∃ v : M, v ≠ 0) ∧
    ∀ W : Submodule ℂ M, IsGL2RealKTypeSubmodule wt E L ε W → W = ⊥ ∨ W = ⊤

theorem isGL2RealKTypeSubmodule_iff (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (W : Submodule ℂ M) :
    IsGL2RealKTypeSubmodule wt E L ε W ↔
      W ≤ (⨆ n : ℤ, W ⊓ wt n) ∧ W.map E ≤ W ∧ W.map L ≤ W ∧ W.map ε ≤ W :=
  Iff.rfl

theorem isIrreducibleGL2RealKTypeModule_iff (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    IsIrreducibleGL2RealKTypeModule wt E L ε ↔
      (∃ v : M, v ≠ 0) ∧
        ∀ W : Submodule ℂ M, IsGL2RealKTypeSubmodule wt E L ε W → W = ⊥ ∨ W = ⊤ :=
  Iff.rfl

theorem isGL2RealKTypeSubmodule_bot (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    IsGL2RealKTypeSubmodule wt E L ε ⊥ := by
  refine ⟨bot_le, ?_, ?_, ?_⟩ <;> simp

theorem isGL2RealKTypeSubmodule_top {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) : IsGL2RealKTypeSubmodule wt E L ε ⊤ := by
  refine ⟨?_, le_top, le_top, le_top⟩
  have htop : (⨆ n : ℤ, wt n) = ⊤ := h.isInternal.submodule_iSup_eq_top
  simp only [top_inf_eq]
  rw [htop]

theorem not_isIrreducibleGL2RealKTypeModule_of_subsingleton [Subsingleton M]
    (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    ¬ IsIrreducibleGL2RealKTypeModule wt E L ε := fun h => by
  obtain ⟨⟨v, hv⟩, -⟩ := h
  exact hv (Subsingleton.elim v 0)

theorem IsGL2RealKTypeModule.refl_comp_lower {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) : ε ∘ₗ L = E ∘ₗ ε := by
  have hεε : ∀ v : M, ε (ε v) = v := fun v => by
    simpa using LinearMap.congr_fun h.refl_comp_refl v
  have hεE : ∀ v : M, ε (E v) = L (ε v) := fun v => by
    simpa using LinearMap.congr_fun h.refl_comp_raise v
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  have := hεE (ε v)
  rw [hεε] at this
  rw [← this, hεε]

theorem IsGL2RealKTypeModule.refl_refl {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) (v : M) : ε (ε v) = v := by
  have := LinearMap.congr_fun h.refl_comp_refl v
  simpa using this

theorem IsGL2RealKTypeModule.raise_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : E v ∈ wt (n + 2) :=
  h.map_raise_le n (Submodule.mem_map_of_mem hv)

theorem IsGL2RealKTypeModule.lower_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : L v ∈ wt (n - 2) :=
  h.map_lower_le n (Submodule.mem_map_of_mem hv)

theorem IsGL2RealKTypeModule.refl_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : ε v ∈ wt (-n) :=
  h.map_refl_le n (Submodule.mem_map_of_mem hv)

end AutomorphicForm

section Battery
open AutomorphicForm
#check @IsGL2RealKTypeModule
#check @IsGL2RealKTypeSubmodule
#check @IsIrreducibleGL2RealKTypeModule
#print axioms AutomorphicForm.isGL2RealKTypeSubmodule_bot
#print axioms AutomorphicForm.isGL2RealKTypeSubmodule_top
#print axioms AutomorphicForm.not_isIrreducibleGL2RealKTypeModule_of_subsingleton
#print axioms AutomorphicForm.IsGL2RealKTypeModule.refl_comp_lower
#print axioms AutomorphicForm.IsGL2RealKTypeModule.refl_refl
end Battery
