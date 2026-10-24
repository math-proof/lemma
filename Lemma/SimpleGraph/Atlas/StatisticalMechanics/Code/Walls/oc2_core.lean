import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc2_core
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc2_corr_covSum_eq_cubeCovSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_corr_covSum_eq_cubeCovSum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) = oc2_cubeCovSum μ (σ : Fin n → E) f := by
-- proof
  apply StatMech.Walls.oc2_corr_covSum_eq_cubeCovSum μ hpos hμ1 σ f

/--
[oc2_corr_mean_eq_cubeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_corr_mean_eq_cubeIntegral_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc2_corr_mean_eq_cubeIntegral μ hpos hμ1 σ f

/--
[oc2_codingCovBridge_cubeFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_codingCovBridge_cubeFrame_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) = oc2_cubeCovSum μ (σ : Fin n → E) f ∧ Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc2_codingCovBridge_cubeFrame μ hpos hμ1 σ f

/--
[oc2_codingCovBridge_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_codingCovBridge_of_residue_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hSum : oc2_SumCovMatch μ ν (σ : Fin n → E) f)
  (hθ : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  oc_CodingCovBridge (ν := ν) f (Lindeberg.mean μ f) (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) := by
-- proof
  apply StatMech.Walls.oc2_codingCovBridge_of_residue μ hpos hμ1 σ ν f hSum hθ

/--
[oc2_correlated_covLowerBound_cubeFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_correlated_covLowerBound_cubeFrame_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {N c₀ D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hcube : N * c₀ * ((∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)) * (1 - ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n))) ≤ D * oc2_cubeCovSum μ (σ : Fin n → E) f) :
-- imply
  N * c₀ * (Lindeberg.mean μ f * (1 - Lindeberg.mean μ f)) ≤ D * ∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e) := by
-- proof
  apply StatMech.Walls.oc2_correlated_covLowerBound_cubeFrame μ hpos hμ1 σ f N c₀ D hcube

/--
[oc2_codingCovBridge_cubeFrame_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_codingCovBridge_cubeFrame_refl_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ} :
-- imply
  (oc2_cubeCovSum μ σ f) = oc2_cubeCovSum μ σ f ∧ (∫ u, f (codeMap μ σ u) ∂(Vcube n)) = ∫ u, f (codeMap μ σ u) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc2_codingCovBridge_cubeFrame_refl μ σ f

/--
[oc2_sumCovMatch_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_sumCovMatch_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ}
  {σ : Fin 0 → E}
  {f : ConfigSpace E → ℝ} :
-- imply
  oc2_SumCovMatch μ ν σ f := by
-- proof
  apply StatMech.Walls.oc2_sumCovMatch_empty μ ν σ f

/--
[oc2_codingCovBridge_of_residue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_codingCovBridge_of_residue_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {σ : Fin 0 ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  oc_CodingCovBridge (ν := ν) f (Lindeberg.mean μ f) (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) := by
-- proof
  apply StatMech.Walls.oc2_codingCovBridge_of_residue_empty μ hpos hμ1 σ ν f

/--
[oc2_fk_codingCovBridge_cubeFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_fk_codingCovBridge_cubeFrame_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ e, Lindeberg.cov (fkMass G p q) f (CovLowerBound.coordI e)) = oc2_cubeCovSum (fkMass G p q) (σ : Fin n → Sym2 V) f ∧ Lindeberg.mean (fkMass G p q) f = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc2_fk_codingCovBridge_cubeFrame G hp hp1 hq σ f

/--
[oc2_fk_codingCovBridge_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean)
-/
@[path]
private lemma oc2_fk_codingCovBridge_of_residue_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {ν : Sym2 V → Bool → ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hSum : oc2_SumCovMatch (fkMass G p q) ν (σ : Fin n → Sym2 V) f)
  (hθ : oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f) :
-- imply
  oc_CodingCovBridge (ν := ν) f (Lindeberg.mean (fkMass G p q) f) (∑ e, Lindeberg.cov (fkMass G p q) f (CovLowerBound.coordI e)) := by
-- proof
  apply StatMech.Walls.oc2_fk_codingCovBridge_of_residue G hp hp1 hq σ ν f hSum hθ


-- created on 2026-10-23
