import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc3_pushforwardlaw
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc3_muPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_muPMF_apply_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  oc3_muPMF μ hpos hμ1 x = ENNReal.ofReal (μ x) := by
-- proof
  apply StatMech.Walls.oc3_muPMF_apply μ hpos hμ1 x

/--
[oc3_muPMF_toMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_muPMF_toMeasure_singleton_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (oc3_muPMF μ hpos hμ1).toMeasure {x} = ENNReal.ofReal (μ x) := by
-- proof
  apply StatMech.Walls.oc3_muPMF_toMeasure_singleton μ hpos hμ1 x

/--
[oc3_pushforward_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_pushforward_singleton_eq
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
  ((Vcube n).map (codeMap μ (σ : Fin n → E))) {x} = ENNReal.ofReal (μ x) := by
-- proof
  apply StatMech.Walls.oc3_pushforward_singleton μ hpos hμ1 σ x

/--
[oc3_pushforward_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_pushforward_law_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (Vcube n).map (codeMap μ (σ : Fin n → E)) = (oc3_muPMF μ hpos hμ1).toMeasure := by
-- proof
  apply StatMech.Walls.oc3_pushforward_law μ hpos hμ1 σ

/--
[oc3_pushforward_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_pushforward_isProbabilityMeasure_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  IsProbabilityMeasure ((Vcube n).map (codeMap μ (σ : Fin n → E))) := by
-- proof
  apply StatMech.Walls.oc3_pushforward_isProbabilityMeasure μ hpos hμ1 σ

/--
[oc3_pushforward_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_pushforward_apply_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {s : Finset (ConfigSpace E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ((Vcube n).map (codeMap μ (σ : Fin n → E))) (s : Set (ConfigSpace E)) = ∑ x ∈ s, ENNReal.ofReal (μ x) := by
-- proof
  apply StatMech.Walls.oc3_pushforward_apply μ hpos hμ1 σ s

/--
[oc3_integral_pushforward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_integral_pushforward_eq
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
  ∫ x, g x ∂((Vcube n).map (codeMap μ (σ : Fin n → E))) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.Walls.oc3_integral_pushforward μ hpos hμ1 σ g

/--
[oc3_fk_pushforward_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_fk_pushforward_law_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (Vcube n).map (codeMap (fkMass G p q) (σ : Fin n → Sym2 V)) = (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω) (fkMass_sum_eq_one G hp hp1 hq)).toMeasure := by
-- proof
  apply StatMech.Walls.oc3_fk_pushforward_law G hp hp1 hq σ

/--
[oc3_fk_pushforward_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_fk_pushforward_singleton_eq
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
  (hq : 0 < q) :
-- imply
  ((Vcube n).map (codeMap (fkMass G p q) (σ : Fin n → Sym2 V))) {x} = ENNReal.ofReal (fkMass G p q x) := by
-- proof
  apply StatMech.Walls.oc3_fk_pushforward_singleton G hp hp1 hq σ x

/--
[oc3_pushforward_singleton_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_pushforward_singleton_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {σ : Fin 0 ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ((Vcube 0).map (codeMap μ (σ : Fin 0 → E))) {x} = ENNReal.ofReal (μ x) := by
-- proof
  apply StatMech.Walls.oc3_pushforward_singleton_empty μ hpos hμ1 σ x

/--
[oc3_pushforward_law_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_pushforwardlaw.lean)
-/
@[path]
private lemma oc3_pushforward_law_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {σ : Fin 0 ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (Vcube 0).map (codeMap μ (σ : Fin 0 → E)) = (oc3_muPMF μ hpos hμ1).toMeasure := by
-- proof
  apply StatMech.Walls.oc3_pushforward_law_empty μ hpos hμ1 σ


-- created on 2026-10-23
