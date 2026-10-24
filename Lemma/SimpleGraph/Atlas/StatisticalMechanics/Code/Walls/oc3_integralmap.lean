import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc3_integralmap
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc3_measurable_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_measurable_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E} :
-- imply
  Measurable (fun u : Fin n → ℝ => codeMap μ (σ : Fin n → E) u) := by
-- proof
  apply StatMech.Walls.oc3_measurable_codeMap μ σ

/--
[oc3_codeLaw_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_codeLaw_apply_eq
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
  (oc3_codeLaw μ σ) {x} = ENNReal.ofReal (μ x) := by
-- proof
  apply StatMech.Walls.oc3_codeLaw_apply μ hpos hμ1 σ x

/--
[oc3_codeLaw_real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_codeLaw_real_singleton_eq
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
  (oc3_codeLaw μ σ).real {x} = μ x := by
-- proof
  apply StatMech.Walls.oc3_codeLaw_real_singleton μ hpos hμ1 σ x

/--
[oc3_integral_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_integral_map_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ} :
-- imply
  ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∫ x, g x ∂(oc3_codeLaw μ σ) := by
-- proof
  apply StatMech.Walls.oc3_integral_map μ σ g

/--
[oc3_integral_codeLaw_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_integral_codeLaw_eq_sum_eq
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
  ∫ x, g x ∂(oc3_codeLaw μ σ) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.Walls.oc3_integral_codeLaw_eq_sum μ hpos hμ1 σ g

/--
[oc3_integralMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_integralMap_eq
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
  ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∫ x, g x ∂(oc3_codeLaw μ σ) ∧ ∫ x, g x ∂(oc3_codeLaw μ σ) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.Walls.oc3_integralMap μ hpos hμ1 σ g

/--
[oc3_integralMap_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_integralMap_eq_sum_eq
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
  apply StatMech.Walls.oc3_integralMap_eq_sum μ hpos hμ1 σ g

/--
[oc3_codeLaw_const_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_codeLaw_const_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ _x, (1 : ℝ) ∂(oc3_codeLaw μ σ) = 1 := by
-- proof
  apply StatMech.Walls.oc3_codeLaw_const_one μ hpos hμ1 σ

/--
[oc3_codeLaw_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_codeLaw_indicator_eq
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
  ∫ y, (if y = x then (1 : ℝ) else 0) ∂(oc3_codeLaw μ σ) = μ x := by
-- proof
  apply StatMech.Walls.oc3_codeLaw_indicator μ hpos hμ1 σ x

/--
[oc3_fk_integralMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_fk_integralMap_eq
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
  (∫ u, g (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) = ∫ x, g x ∂(oc3_codeLaw (fkMass G p q) σ)) ∧ (∫ x, g x ∂(oc3_codeLaw (fkMass G p q) σ) = ∑ x, g x * fkMass G p q x) := by
-- proof
  apply StatMech.Walls.oc3_fk_integralMap G hp hp1 hq σ g

/--
[oc3_fk_codeLaw_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean)
-/
@[path]
private lemma oc3_fk_codeLaw_apply_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {x : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (oc3_codeLaw (fkMass G p q) σ) {x} = ENNReal.ofReal (fkMass G p q x) := by
-- proof
  apply StatMech.Walls.oc3_fk_codeLaw_apply G hp hp1 hq σ x


-- created on 2026-10-23
