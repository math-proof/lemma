import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc4_firstedgeone
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc4_revealAdapt_first_as_cubeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_revealAdapt_first_as_cubeIntegral_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  revealAdapt μ σ f e = ∫ u, truncIndC σ f (codeMap μ (σ : Fin n → E) u) ((σ.symm e : ℕ) + 1) ∂(Vcube n) := by
-- proof
  apply StatMech.Walls.oc4_revealAdapt_first_as_cubeIntegral μ σ f e

/--
[oc4_revealAdapt_first_eq_one_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_revealAdapt_first_eq_one_codingFrame_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X) :
-- imply
  revealAdapt μ σ f e₀ = 1 := by
-- proof
  apply StatMech.Walls.oc4_revealAdapt_first_eq_one_codingFrame hpos hμ1 σ f e₀ he₀ hnc

/--
[oc4_revealAdapt_first_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_revealAdapt_first_gt_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
  {c : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hc : c < 1) :
-- imply
  ¬ revealAdapt μ σ f e₀ ≤ c := by
-- proof
  apply StatMech.Walls.oc4_revealAdapt_first_gt hpos hμ1 σ f e₀ he₀ hnc hc

/--
[oc4_not_forall_revealAdapt_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_not_forall_revealAdapt_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
  {c : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hc : c < 1) :
-- imply
  ¬ (∀ e, revealAdapt μ σ f e ≤ c) := by
-- proof
  apply StatMech.Walls.oc4_not_forall_revealAdapt_le hpos hμ1 σ f e₀ he₀ hnc hc

/--
[oc4_fk_revealAdapt_first_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_fk_revealAdapt_first_eq_one_eq
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
  {e₀ : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X) :
-- imply
  revealAdapt (fkMass G p q) σ f e₀ = 1 := by
-- proof
  apply StatMech.Walls.oc4_fk_revealAdapt_first_eq_one G hp hp1 hq σ f e₀ he₀ hnc

/--
[oc4_uniform_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_uniform_sum_eq_one_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  (∑ _ω : ConfigSpace (Fin 2), 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) = 1 := by
-- proof
  apply StatMech.Walls.oc4_uniform_sum_eq_one

/--
[oc4_coord_nonconstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_coord_nonconstant_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∀ X : ConfigSpace (Fin 2), ¬ ∀ w, Lindeberg.coord (0 : Fin 2) w = Lindeberg.coord 0 X := by
-- proof
  apply StatMech.Walls.oc4_coord_nonconstant

/--
[oc4_first_edge_one_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_first_edge_one_witness_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) = 1 := by
-- proof
  apply StatMech.Walls.oc4_first_edge_one_witness

/--
[oc4_not_forall_revealAdapt_le_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_firstedgeone.lean)
-/
@[path]
private lemma oc4_not_forall_revealAdapt_le_witness_eq
  [Fintype E]
  [DecidableEq E]
  {c : ℝ}
-- given
  (hc : c < 1) :
-- imply
  ¬ (∀ e : Fin 2, revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) e ≤ c) := by
-- proof
  apply StatMech.Walls.oc4_not_forall_revealAdapt_le_witness hc


-- created on 2026-10-23
