import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc4_codingframe
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc4_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_codingFrame_eq
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
  apply StatMech.Walls.oc4_codingFrame μ hpos hμ1 σ f

/--
[oc4_codingFrame_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_codingFrame_symm_eq
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
  (∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)) = Lindeberg.mean μ f := by
-- proof
  apply StatMech.Walls.oc4_codingFrame_symm μ hpos hμ1 σ f

/--
[oc4_codingFrame_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_codingFrame_indicator_eq
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
  μ x = ∫ u, (if codeMap μ (σ : Fin n → E) u = x then (1 : ℝ) else 0) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_codingFrame_indicator μ hpos hμ1 σ x

/--
[oc4_codingFrame_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_codingFrame_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (1 : ℝ) = ∫ _u, (1 : ℝ) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_codingFrame_one μ hpos hμ1 σ

/--
[oc4_codingFrame_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_codingFrame_const_eq
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
  apply StatMech.Walls.oc4_codingFrame_const μ hpos hμ1 σ c

/--
[oc4_codingFrame_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_codingFrame_linear_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {a b : ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.mean μ (fun ω => a * f ω + b * g ω) = ∫ u, (a * f (codeMap μ (σ : Fin n → E) u) + b * g (codeMap μ (σ : Fin n → E) u)) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_codingFrame_linear μ hpos hμ1 σ a b f g

/--
[oc4_codingFrame_noProductWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_codingFrame_noProductWeight_eq
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
  (¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧ ∀ g, expect ν g = Lindeberg.mean μ g) ∧ (∀ f, Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)) := by
-- proof
  apply StatMech.Walls.oc4_codingFrame_noProductWeight μ hpos hμ1 σ hcorr

/--
[oc4_cf_fk_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_cf_fk_codingFrame_eq
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
  apply StatMech.Walls.oc4_cf_fk_codingFrame G hp hp1 hq σ f

/--
[oc4_cf_fk_codingFrame_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_codingframe.lean)
-/
@[path]
private lemma oc4_cf_fk_codingFrame_indicator_eq
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
  fkMass G p q x = ∫ u, (if codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u = x then (1 : ℝ) else 0) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_cf_fk_codingFrame_indicator G hp hp1 hq σ x


-- created on 2026-10-23
