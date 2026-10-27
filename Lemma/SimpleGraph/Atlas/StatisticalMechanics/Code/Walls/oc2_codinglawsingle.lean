import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc2_codinglawsingle
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc2_coding_fibre_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawsingle.lean)
-/
@[path]
private lemma oc2_coding_fibre_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x := by
-- proof
  apply StatMech.Walls.oc2_coding_fibre_mass μ hpos hμ1 σ x

/--
[oc2_coding_law_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawsingle.lean)
-/
@[path]
private lemma oc2_coding_law_single_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.Walls.oc2_coding_law_single μ hpos hμ1 σ g

/--
[oc2_coding_law_single_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawsingle.lean)
-/
@[path]
private lemma oc2_coding_law_single_expect_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.Walls.oc2_coding_law_single_expect μ hpos hμ1 σ g

/--
[oc2_coding_law_const_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawsingle.lean)
-/
@[path]
private lemma oc2_coding_law_const_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ _u, (1 : ℝ) ∂(Vcube n) = 1 := by
-- proof
  apply StatMech.Walls.oc2_coding_law_const_one μ hpos hμ1 σ

/--
[oc2_coding_law_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawsingle.lean)
-/
@[path]
private lemma oc2_coding_law_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ u, (if codeMap μ (σ : Fin n → E) u = x then (1 : ℝ) else 0) ∂(Vcube n) = μ x := by
-- proof
  apply StatMech.Walls.oc2_coding_law_indicator μ hpos hμ1 σ x


-- created on 2026-10-23
