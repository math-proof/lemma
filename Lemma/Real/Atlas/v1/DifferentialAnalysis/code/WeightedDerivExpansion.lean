import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.WeightedDerivExpansion.Part2
open BigOperators WeightedDerivExpansion
open scoped SchwartzMap


namespace WeightedDerivExpansion

/--
[diff_size_update_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeightedDerivExpansion.lean)
-/
@[path]
lemma diff_size_update_lt
  {n : ℕ}
  {γ α : Fin n → ℕ}
  {j₀ : Fin n}
-- given
  (hj₀ : 0 < γ j₀)
  (hα : multiIndexLE α (Function.update γ j₀ (γ j₀ - 1))) :
-- imply
  1 + multiIndexDiffSize (Function.update γ j₀ (γ j₀ - 1)) α ≤ multiIndexDiffSize γ α := by
-- proof
  simp only [multiIndexDiffSize]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have htail : ∀ i ∈ Finset.univ.erase j₀,
    Function.update γ j₀ (γ j₀ - 1) i - α i = γ i - α i := fun i hi =>
    congrArg (· - α i) (Function.update_of_ne (Finset.ne_of_mem_erase hi) (γ j₀ - 1) γ)
  rw [Finset.sum_congr rfl htail, Function.update_self]
  have : α j₀ ≤ γ j₀ - 1 := by
    have := hα j₀; rwa [Function.update_self] at this
  omega
end WeightedDerivExpansion



-- created on 2026-10-23
