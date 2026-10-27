import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DetLoopExpansion
open Polynomial Set FiniteDimensional Module StatMech StatMech.Onsager


/--
[trace_pow_endo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetLoopExpansion.lean)
-/
@[path]
private lemma trace_pow_endo_eq
  [AddCommGroup V]
  [Module ℂ V]
  [FiniteDimensional ℂ V]
  {φ : Module.End ℂ V}
  {k : ℕ} :
-- imply
  LinearMap.trace ℂ V (φ ^ k) = (φ.charpoly.roots.map (fun α => α ^ k)).sum := by
-- proof
  apply StatMech.Onsager.trace_pow_endo φ k

/--
[ons_det_loop_expansion_of_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetLoopExpansion.lean)
-/
@[path]
private lemma ons_det_loop_expansion_of_trace_eq
  [Fintype ι]
  [DecidableEq ι]
  {Λ : Matrix ι ι ℂ}
-- given
  (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1)
  (htrace : ∀ n : ℕ, (Λ ^ (n + 1)).trace = (Λ.charpoly.roots.map (fun α => α ^ (n + 1))).sum) :
-- imply
  (1 - Λ).det = Complex.exp (- ∑' n : ℕ, (Λ ^ (n + 1)).trace / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_det_loop_expansion_of_trace Λ hspec htrace

/--
[ons_det_loop_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetLoopExpansion.lean)
-/
@[path]
private lemma ons_det_loop_expansion_eq
  [Fintype ι]
  [DecidableEq ι]
  {Λ : Matrix ι ι ℂ}
-- given
  (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
-- imply
  (1 - Λ).det = Complex.exp (- ∑' n : ℕ, (Λ ^ (n + 1)).trace / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_det_loop_expansion Λ hspec


-- created on 2026-10-23
