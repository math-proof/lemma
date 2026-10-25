import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.CouplingStructure
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.CouplingStructure


/--
[osss_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CouplingStructure.lean)
-/
@[path]
private lemma osss_coupling_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U V : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) 0)) = f (codeMap μ (σ : Fin n → E) U)) ∧ (∀ (h : ConfigSpace E → ConfigSpace E → ℝ) {Ch : ℝ}, (∀ x y, |h x y| ≤ Ch) → ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n)) ∂((Vcube n).prod (Vcube n)) = ∑ x, (∑ y, h x y * μ y) * μ x) ∧ (∀ t : ℕ, stopVal μ σ f U < t → codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t) = codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t - 1))) := by
-- proof
  apply StatMech.OSSS.CouplingStructure.osss_coupling hpos hμ1 σ U V


-- created on 2026-10-23
