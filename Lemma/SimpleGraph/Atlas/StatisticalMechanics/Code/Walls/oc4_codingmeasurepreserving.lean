import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc4_codingmeasurepreserving
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc4_coding_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_coding_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  MeasurePreserving (codeMap μ (σ : Fin n → E)) (Vcube n) (oc3_muPMF μ hpos hμ1).toMeasure := by
-- proof
  apply StatMech.Walls.oc4_coding_measurePreserving μ hpos hμ1 σ

/--
[oc4_codingMeasurePreserving_to_codeLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_codingMeasurePreserving_to_codeLaw_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E} :
-- imply
  MeasurePreserving (codeMap μ (σ : Fin n → E)) (Vcube n) (oc3_codeLaw μ σ) := by
-- proof
  apply StatMech.Walls.oc4_codingMeasurePreserving_to_codeLaw μ σ

/--
[oc4_coding_preimage_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_coding_preimage_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {s : Set (ConfigSpace E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (Vcube n) (codeMap μ (σ : Fin n → E) ⁻¹' s) = (oc3_muPMF μ hpos hμ1).toMeasure s := by
-- proof
  apply StatMech.Walls.oc4_coding_preimage_mass μ hpos hμ1 σ s

/--
[oc4_coding_preimage_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_coding_preimage_singleton_eq
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
  (Vcube n) (codeMap μ (σ : Fin n → E) ⁻¹' {x}) = ENNReal.ofReal (μ x) := by
-- proof
  apply StatMech.Walls.oc4_coding_preimage_singleton μ hpos hμ1 σ x

/--
[oc4_coding_measurePreserving_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_coding_measurePreserving_integral_eq
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
  ∫ x, g x ∂((oc3_muPMF μ hpos hμ1).toMeasure) = ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) ∧ ∫ x, g x ∂((oc3_muPMF μ hpos hμ1).toMeasure) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.Walls.oc4_coding_measurePreserving_integral μ hpos hμ1 σ g

/--
[oc4_fk_coding_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_fk_coding_measurePreserving_eq
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
  MeasurePreserving (codeMap (fkMass G p q) (σ : Fin n → Sym2 V)) (Vcube n) (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω) (fkMass_sum_eq_one G hp hp1 hq)).toMeasure := by
-- proof
  apply StatMech.Walls.oc4_fk_coding_measurePreserving G hp hp1 hq σ

/--
[oc4_fk_coding_preimage_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_fk_coding_preimage_mass_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {s : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (Vcube n) (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) ⁻¹' s) = (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω) (fkMass_sum_eq_one G hp hp1 hq)).toMeasure s := by
-- proof
  apply StatMech.Walls.oc4_fk_coding_preimage_mass G hp hp1 hq σ s

/--
[oc4_coding_target_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_coding_target_isProbabilityMeasure_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  IsProbabilityMeasure ((oc3_muPMF μ hpos hμ1).toMeasure) := by
-- proof
  apply StatMech.Walls.oc4_coding_target_isProbabilityMeasure μ hpos hμ1

/--
[oc4_coding_preimage_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_coding_preimage_univ_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (Vcube n) (codeMap μ (σ : Fin n → E) ⁻¹' (Set.univ)) = 1 := by
-- proof
  apply StatMech.Walls.oc4_coding_preimage_univ μ hpos hμ1 σ

/--
[oc4_coding_measurePreserving_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingmeasurepreserving.lean)
-/
@[path]
private lemma oc4_coding_measurePreserving_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {σ : Fin 0 ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  MeasurePreserving (codeMap μ (σ : Fin 0 → E)) (Vcube 0) (oc3_muPMF μ hpos hμ1).toMeasure := by
-- proof
  apply StatMech.Walls.oc4_coding_measurePreserving_empty μ hpos hμ1 σ


-- created on 2026-10-23
