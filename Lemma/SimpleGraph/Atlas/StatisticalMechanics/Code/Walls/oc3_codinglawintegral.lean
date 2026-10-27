import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc3_codinglawintegral
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc3_codingFibreMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codinglawintegral.lean)
-/
@[path]
private lemma oc3_codingFibreMass_eq
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
  apply StatMech.Walls.oc3_codingFibreMass μ hpos hμ1 σ x

/--
[oc3_codingLawIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codinglawintegral.lean)
-/
@[path]
private lemma oc3_codingLawIntegral_eq
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
  apply StatMech.Walls.oc3_codingLawIntegral μ hpos hμ1 σ g

/--
[oc3_codingLawIntegral_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codinglawintegral.lean)
-/
@[path]
private lemma oc3_codingLawIntegral_expect_eq
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
  apply StatMech.Walls.oc3_codingLawIntegral_expect μ hpos hμ1 σ g

/--
[oc3_codingLawIntegral_const_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codinglawintegral.lean)
-/
@[path]
private lemma oc3_codingLawIntegral_const_one_eq
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
  apply StatMech.Walls.oc3_codingLawIntegral_const_one μ hpos hμ1 σ

/--
[oc3_codingLawIntegral_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codinglawintegral.lean)
-/
@[path]
private lemma oc3_codingLawIntegral_indicator_eq
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
  apply StatMech.Walls.oc3_codingLawIntegral_indicator μ hpos hμ1 σ x

/--
[oc3_fk_codingLawIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codinglawintegral.lean)
-/
@[path]
private lemma oc3_fk_codingLawIntegral_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ∫ u, g (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) = ∑ x, g x * fkMass G p q x := by
-- proof
  apply StatMech.Walls.oc3_fk_codingLawIntegral G hp hp1 hq σ g


-- created on 2026-10-23
