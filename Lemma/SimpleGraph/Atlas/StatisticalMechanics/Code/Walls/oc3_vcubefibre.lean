import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc3_vcubefibre
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc3_fibre_eq_rawbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubefibre.lean)
-/
@[path]
private lemma oc3_fibre_eq_rawbox_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E} :
-- imply
  {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} = Set.univ.pi (fun t => rawInterval μ (σ : Fin n → E) x t) := by
-- proof
  apply StatMech.Walls.oc3_fibre_eq_rawbox μ σ x

/--
[oc3_rawInterval_marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubefibre.lean)
-/
@[path]
private lemma oc3_rawInterval_marginal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
  {t : Fin n}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (volume.restrict (Set.Icc (0 : ℝ) 1) (rawInterval μ (σ : Fin n → E) x t)).toReal = condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x ((σ : Fin n → E) t) (x ((σ : Fin n → E) t)) := by
-- proof
  apply StatMech.Walls.oc3_rawInterval_marginal μ hpos σ x t

/--
[oc3_marginals_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubefibre.lean)
-/
@[path]
private lemma oc3_marginals_telescope_eq
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
  (∏ t : Fin n, condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x ((σ : Fin n → E) t) (x ((σ : Fin n → E) t))) = μ x := by
-- proof
  apply StatMech.Walls.oc3_marginals_telescope μ hpos hμ1 σ x

/--
[oc3_vcube_fibre_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubefibre.lean)
-/
@[path]
private lemma oc3_vcube_fibre_prod_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = ∏ t : Fin n, condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x ((σ : Fin n → E) t) (x ((σ : Fin n → E) t)) := by
-- proof
  apply StatMech.Walls.oc3_vcube_fibre_prod μ hpos σ x

/--
[oc3_vcube_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubefibre.lean)
-/
@[path]
private lemma oc3_vcube_fibre_eq
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
  apply StatMech.Walls.oc3_vcube_fibre μ hpos hμ1 σ x

/--
[oc3_vcube_total_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubefibre.lean)
-/
@[path]
private lemma oc3_vcube_total_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (∑ x : ConfigSpace E, ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal) = 1 := by
-- proof
  apply StatMech.Walls.oc3_vcube_total_mass μ hpos hμ1 σ


-- created on 2026-10-23
