import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc_firstedgerevealone
open StatMech StatMech.Walls


/--
[oc_revealAdapt_first_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_firstedgerevealone.lean)
-/
@[path]
private lemma oc_revealAdapt_first_eq_one_eq
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
  apply StatMech.Walls.oc_revealAdapt_first_eq_one hpos hμ1 σ f e₀ he₀ hnc

/--
[oc_revealAdapt_first_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_firstedgerevealone.lean)
-/
@[path]
private lemma oc_revealAdapt_first_gt_eq
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
  apply StatMech.Walls.oc_revealAdapt_first_gt hpos hμ1 σ f e₀ he₀ hnc hc

/--
[oc_not_forall_revealAdapt_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_firstedgerevealone.lean)
-/
@[path]
private lemma oc_not_forall_revealAdapt_le_eq
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
  apply StatMech.Walls.oc_not_forall_revealAdapt_le hpos hμ1 σ f e₀ he₀ hnc hc

/--
[oc_uniform_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_firstedgerevealone.lean)
-/
@[path]
private lemma oc_uniform_sum_eq_one_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  (∑ _ω : ConfigSpace (Fin 2), 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) = 1 := by
-- proof
  apply StatMech.Walls.oc_uniform_sum_eq_one

/--
[oc_coord_nonconstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_firstedgerevealone.lean)
-/
@[path]
private lemma oc_coord_nonconstant_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∀ X : ConfigSpace (Fin 2), ¬ ∀ w, Lindeberg.coord (0 : Fin 2) w = Lindeberg.coord 0 X := by
-- proof
  apply StatMech.Walls.oc_coord_nonconstant

/--
[oc_first_edge_reveal_one_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_firstedgerevealone.lean)
-/
@[path]
private lemma oc_first_edge_reveal_one_witness_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) = 1 := by
-- proof
  apply StatMech.Walls.oc_first_edge_reveal_one_witness

/--
[oc_not_forall_revealAdapt_le_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_firstedgerevealone.lean)
-/
@[path]
private lemma oc_not_forall_revealAdapt_le_witness_eq
  [Fintype E]
  [DecidableEq E]
  {c : ℝ}
-- given
  (hc : c < 1) :
-- imply
  ¬ (∀ e : Fin 2, revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) e ≤ c) := by
-- proof
  apply StatMech.Walls.oc_not_forall_revealAdapt_le_witness hc


-- created on 2026-10-23
