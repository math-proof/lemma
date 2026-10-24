import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc3_codemapmeasurable
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc3_codeMap_fibre_eq_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codemapmeasurable.lean)
-/
@[path]
private lemma oc3_codeMap_fibre_eq_iInter_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E} :
-- imply
  {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} = ⋂ t : Fin n, {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)} := by
-- proof
  apply StatMech.Walls.oc3_codeMap_fibre_eq_iInter μ σ x

/--
[oc3_codeMap_fibre_coord_eq_halfLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codemapmeasurable.lean)
-/
@[path]
private lemma oc3_codeMap_fibre_coord_eq_halfLine_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
  {t : Fin n} :
-- imply
  {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)} = (if x ((σ : Fin n → E) t) then {u : Fin n → ℝ | u t ≥ thr μ (σ : Fin n → E) x t} else {u : Fin n → ℝ | u t < thr μ (σ : Fin n → E) x t}) := by
-- proof
  apply StatMech.Walls.oc3_codeMap_fibre_coord_eq_halfLine μ σ x t

/--
[oc3_measurableSet_codeMap_fibre_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codemapmeasurable.lean)
-/
@[path]
private lemma oc3_measurableSet_codeMap_fibre_coord_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
  {t : Fin n} :
-- imply
  MeasurableSet {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)} := by
-- proof
  apply StatMech.Walls.oc3_measurableSet_codeMap_fibre_coord μ σ x t

/--
[oc3_measurableSet_codeMap_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codemapmeasurable.lean)
-/
@[path]
private lemma oc3_measurableSet_codeMap_fibre_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E} :
-- imply
  MeasurableSet {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} := by
-- proof
  apply StatMech.Walls.oc3_measurableSet_codeMap_fibre μ σ x

/--
[oc3_codemap_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codemapmeasurable.lean)
-/
@[path]
private lemma oc3_codemap_measurable_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E} :
-- imply
  Measurable (fun u : Fin n → ℝ => codeMap μ (σ : Fin n → E) u) := by
-- proof
  apply StatMech.Walls.oc3_codemap_measurable μ σ

/--
[oc3_measurable_g_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_codemapmeasurable.lean)
-/
@[path]
private lemma oc3_measurable_g_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ} :
-- imply
  Measurable (fun u : Fin n → ℝ => g (codeMap μ (σ : Fin n → E) u)) := by
-- proof
  apply StatMech.Walls.oc3_measurable_g_codeMap μ σ g


-- created on 2026-10-23
