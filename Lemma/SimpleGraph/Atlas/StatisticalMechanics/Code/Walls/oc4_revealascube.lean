import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc4_revealascube
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc4_revealAsCube_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealascube.lean)
-/
@[path]
private lemma oc4_revealAsCube_collapse_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ} :
-- imply
  (∫ p, truncInd μ σ f p.1 t ∂((Vcube n).prod (Vcube n))) = ∫ U, truncInd μ σ f U t ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_revealAsCube_collapse μ σ f t

/--
[oc4_revealAsCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealascube.lean)
-/
@[path]
private lemma oc4_revealAsCube_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X := by
-- proof
  apply StatMech.Walls.oc4_revealAsCube μ hpos hμ1 σ f e

/--
[oc4_revealAsCube_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealascube.lean)
-/
@[path]
private lemma oc4_revealAsCube_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = Lindeberg.mean μ (fun X => truncIndC σ f X ((σ.symm e : ℕ) + 1)) := by
-- proof
  apply StatMech.Walls.oc4_revealAsCube_mean μ hpos hμ1 σ f e

/--
[oc4_revealAsCube_cubeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealascube.lean)
-/
@[path]
private lemma oc4_revealAsCube_cubeIntegral_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = ∫ U, truncIndC σ f (codeMap μ (σ : Fin n → E) U) ((σ.symm e : ℕ) + 1) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_revealAsCube_cubeIntegral μ hpos hμ1 σ f e

/--
[oc4_fk_revealAsCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealascube.lean)
-/
@[path]
private lemma oc4_fk_revealAsCube_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  revealAdapt (fkMass G p 2) σ f e = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * fkMass G p 2 X := by
-- proof
  apply StatMech.Walls.oc4_fk_revealAsCube G hp hp1 σ f e

/--
[oc4_revealAsCube_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealascube.lean)
-/
@[path]
private lemma oc4_revealAsCube_const_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = ∑ X ∈ Finset.univ.filter (fun X => ((σ.symm e : ℕ) + 1) ≤ stopValC σ f X), μ X := by
-- proof
  apply StatMech.Walls.oc4_revealAsCube_const μ hpos hμ1 σ f e

/--
[oc4_revealAsCube_mean_const_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealascube.lean)
-/
@[path]
private lemma oc4_revealAsCube_mean_const_one_eq
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
  Lindeberg.mean μ (fun X => truncIndC σ f X 0) = 1 := by
-- proof
  apply StatMech.Walls.oc4_revealAsCube_mean_const_one μ hpos hμ1 σ f


-- created on 2026-10-23
