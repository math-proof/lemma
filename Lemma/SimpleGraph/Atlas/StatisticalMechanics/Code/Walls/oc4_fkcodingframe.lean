import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc4_fkcodingframe
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc4_fk_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_codingFrame_eq
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
  apply StatMech.Walls.oc4_fk_codingFrame G hp hp1 hq σ f

/--
[oc4_fk_codingFrame_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_codingFrame_sum_eq
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
  (∑ x, f x * fkMass G p q x) = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_fk_codingFrame_sum G hp hp1 hq σ f

/--
[oc4_fk_codingFrame_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_codingFrame_measurePreserving_eq
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
  apply StatMech.Walls.oc4_fk_codingFrame_measurePreserving G hp hp1 hq σ

/--
[oc4_fk_codingFrame_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_codingFrame_indicator_eq
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
  ∫ u, (if codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u = x then (1 : ℝ) else 0) ∂(Vcube n) = fkMass G p q x := by
-- proof
  apply StatMech.Walls.oc4_fk_codingFrame_indicator G hp hp1 hq σ x

/--
[oc4_fk_codingFrame_total_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_codingFrame_total_mass_eq
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
  ∫ _u, (1 : ℝ) ∂(Vcube n) = 1 := by
-- proof
  apply StatMech.Walls.oc4_fk_codingFrame_total_mass G hp hp1 hq σ

/--
[oc4_fk_correlated_covLowerBound_cubeFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_correlated_covLowerBound_cubeFrame_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {N c₀ D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hcube : N * c₀ * ((∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n)) * (1 - ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n))) ≤ D * oc2_cubeCovSum (fkMass G p q) (σ : Fin n → Sym2 V) f) :
-- imply
  N * c₀ * (Lindeberg.mean (fkMass G p q) f * (1 - Lindeberg.mean (fkMass G p q) f)) ≤ D * ∑ e, Lindeberg.cov (fkMass G p q) f (CovLowerBound.coordI e) := by
-- proof
  apply StatMech.Walls.oc4_fk_correlated_covLowerBound_cubeFrame G hp hp1 hq σ f N c₀ D hcube

/--
[oc4_fk_codingFrame_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_codingFrame_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {c : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Lindeberg.mean (fkMass G p q) (fun _ => c) = ∫ _u, c ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_fk_codingFrame_const G hp hp1 hq σ c

/--
[oc4_fk_codingFrame_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_fkcodingframe.lean)
-/
@[path]
private lemma oc4_fk_codingFrame_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [IsEmpty (Sym2 V)]
  {p q : ℝ}
  {σ : Fin 0 ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Lindeberg.mean (fkMass G p q) f = ∫ u, f (codeMap (fkMass G p q) (σ : Fin 0 → Sym2 V) u) ∂(Vcube 0) := by
-- proof
  apply StatMech.Walls.oc4_fk_codingFrame_empty G hp hp1 hq σ f


-- created on 2026-10-23
