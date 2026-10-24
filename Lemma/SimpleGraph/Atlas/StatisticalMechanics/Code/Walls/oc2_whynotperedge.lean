import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc2_whynotperedge
open Finset StatMech StatMech.Walls


/--
[oc2_reveal_lt_one_of_missing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_reveal_lt_one_of_missing_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
  {ω₀ : ConfigSpace E}
-- given
  (hν : IsProbWeight ν)
  (hw₀ : 0 < weight ν ω₀)
  (hmiss : e ∉ T.queried ω₀) :
-- imply
  reveal ν T e < 1 := by
-- proof
  apply StatMech.Walls.oc2_reveal_lt_one_of_missing hν T e ω₀ hw₀ hmiss

/--
[oc2_revealAdapt_first_ne_reveal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_revealAdapt_first_ne_reveal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hlt : reveal ν T e₀ < 1) :
-- imply
  revealAdapt μ σ f e₀ ≠ reveal ν T e₀ := by
-- proof
  apply StatMech.Walls.oc2_revealAdapt_first_ne_reveal hpos hμ1 σ f e₀ he₀ hnc T hlt

/--
[oc2_revealAdapt_first_ne_reveal_of_missing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_revealAdapt_first_ne_reveal_of_missing_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {ω₀ : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hν : IsProbWeight ν)
  (hw₀ : 0 < weight ν ω₀)
  (hmiss : e₀ ∉ T.queried ω₀) :
-- imply
  revealAdapt μ σ f e₀ ≠ reveal ν T e₀ := by
-- proof
  apply StatMech.Walls.oc2_revealAdapt_first_ne_reveal_of_missing hpos hμ1 σ f e₀ he₀ hnc hν T ω₀ hw₀ hmiss

/--
[oc2_no_perEdge_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_no_perEdge_match_eq
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
  ¬ ∃ (ν : E → Bool → ℝ) (T : DecisionTree E), reveal ν T e₀ < 1 ∧ revealAdapt μ σ f e₀ = reveal ν T e₀ := by
-- proof
  apply StatMech.Walls.oc2_no_perEdge_match hpos hμ1 σ f e₀ he₀ hnc

/--
[oc2_perEdge_match_forces_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_perEdge_match_forces_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hmatch : revealAdapt μ σ f e₀ = reveal ν T e₀) :
-- imply
  reveal ν T e₀ = 1 := by
-- proof
  apply StatMech.Walls.oc2_perEdge_match_forces_one hpos hμ1 σ f e₀ he₀ hnc T hmatch

/--
[oc2_not_forall_revealAdapt_eq_reveal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_not_forall_revealAdapt_eq_reveal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hlt : reveal ν T e₀ < 1) :
-- imply
  ¬ (∀ e, revealAdapt μ σ f e = reveal ν T e) := by
-- proof
  apply StatMech.Walls.oc2_not_forall_revealAdapt_eq_reveal hpos hμ1 σ f e₀ he₀ hnc T hlt

/--
[oc2_uniformWeight_isProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_uniformWeight_isProb_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  IsProbWeight (fun (_ : Fin 2) (_ : Bool) => (1 : ℝ) / 2) where nonneg := by
-- proof
  apply StatMech.Walls.oc2_uniformWeight_isProb

/--
[oc2_reveal_leaf_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_reveal_leaf_eq_zero_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {b : Bool}
  {e : E} :
-- imply
  reveal ν (DecisionTree.leaf b) e = 0 := by
-- proof
  apply StatMech.Walls.oc2_reveal_leaf_eq_zero b e

/--
[oc2_revealAdapt_first_ne_reveal_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_whynotperedge.lean)
-/
@[path]
private lemma oc2_revealAdapt_first_ne_reveal_witness_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) ≠ reveal (fun (_ : Fin 2) (_ : Bool) => (1 : ℝ) / 2) (DecisionTree.leaf false) (0 : Fin 2) := by
-- proof
  apply StatMech.Walls.oc2_revealAdapt_first_ne_reveal_witness


-- created on 2026-10-23
