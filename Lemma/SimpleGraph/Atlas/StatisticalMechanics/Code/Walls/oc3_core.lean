import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc3_core
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc3_expectAsCube_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_expectAsCube_codingFrame_eq
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
  apply StatMech.Walls.oc3_expectAsCube_codingFrame μ hpos hμ1 σ f

/--
[oc3_codingFrame_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_codingFrame_measurePreserving_eq
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
  apply StatMech.Walls.oc3_codingFrame_measurePreserving μ hpos hμ1 σ

/--
[oc3_expectAsCube_codingFrame_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_expectAsCube_codingFrame_triple_eq
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
  Lindeberg.mean μ f = ∫ x, f x ∂(oc3_codeLaw μ σ) ∧ (∫ x, f x ∂(oc3_codeLaw μ σ)) = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc3_expectAsCube_codingFrame_triple μ hpos hμ1 σ f

/--
[oc3_expectAsCubeAt_iff_meanMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_expectAsCubeAt_iff_meanMatch_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f ↔ expect ν f = Lindeberg.mean μ f := by
-- proof
  apply StatMech.Walls.oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν f

/--
[oc3_expectAsCubeAt_of_meanMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_expectAsCubeAt_of_meanMatch_eq
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
  (hmatch : expect ν f = Lindeberg.mean μ f) :
-- imply
  oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f := by
-- proof
  apply StatMech.Walls.oc3_expectAsCubeAt_of_meanMatch μ hpos hμ1 σ ν f hmatch

/--
[oc3_expectAsCubeAt_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_expectAsCubeAt_of_const_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {c : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hν : IsProbWeight ν) :
-- imply
  oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) (fun _ => c) := by
-- proof
  apply StatMech.Walls.oc3_expectAsCubeAt_of_const μ hpos hμ1 σ hν c

/--
[oc3_no_general_product_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_no_general_product_frame_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hcorr : oc3_GenuinelyCorrelated μ) :
-- imply
  ¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧ ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f := by
-- proof
  apply StatMech.Walls.oc3_no_general_product_frame μ hpos hμ1 σ hcorr

/--
[oc3_fk_expectAsCube_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_fk_expectAsCube_codingFrame_eq
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
  Lindeberg.mean (fkMass G p q) f = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc3_fk_expectAsCube_codingFrame G hp hp1 hq σ f

/--
[oc3_fk_codingFrame_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_fk_codingFrame_measurePreserving_eq
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
  apply StatMech.Walls.oc3_fk_codingFrame_measurePreserving G hp hp1 hq σ

/--
[oc3_expectAsCube_codingFrame_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_expectAsCube_codingFrame_const_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {c : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.mean μ (fun _ => c) = ∫ _u, c ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc3_expectAsCube_codingFrame_const μ hpos hμ1 σ c

/--
[oc3_expectAsCubeAt_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_core.lean)
-/
@[path]
private lemma oc3_expectAsCubeAt_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ}
  {σ : Fin 0 ≃ E}
  {f : ConfigSpace E → ℝ} :
-- imply
  oc2_ExpectAsCubeAt ν μ (σ : Fin 0 → E) f := by
-- proof
  apply StatMech.Walls.oc3_expectAsCubeAt_empty μ ν σ f


-- created on 2026-10-23
