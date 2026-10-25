import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc4_noproductweight.Part2
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc4_allF_match_meanMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_allF_match_meanMatch_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  ∀ g, expect ν g = Lindeberg.mean μ g := by
-- proof
  apply StatMech.Walls.oc4_allF_match_meanMatch μ hpos hμ1 σ ν hall

/--
[oc4_allF_match_forces_uncorrelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_allF_match_forces_uncorrelated_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {e e' : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hν : IsProbWeight ν)
  (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f)
  (he : e ≠ e') :
-- imply
  Lindeberg.cov μ (Lindeberg.coord e) (Lindeberg.coord e') = 0 := by
-- proof
  apply StatMech.Walls.oc4_allF_match_forces_uncorrelated μ hpos hμ1 σ hν hall e e' he

/--
[oc4_no_product_weight_expectAsCubeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_no_product_weight_expectAsCubeAt_eq
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
  apply StatMech.Walls.oc4_no_product_weight_expectAsCubeAt μ hpos hμ1 σ hcorr

/--
[oc4_allF_match_not_genuinelyCorrelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_allF_match_not_genuinelyCorrelated_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hν : IsProbWeight ν)
  (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  ¬ oc3_GenuinelyCorrelated μ := by
-- proof
  apply StatMech.Walls.oc4_allF_match_not_genuinelyCorrelated μ hpos hμ1 σ hν hall

/--
[oc4_allF_match_iff_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_allF_match_iff_weight_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) ↔ (∀ ω, weight ν ω = μ ω) := by
-- proof
  apply StatMech.Walls.oc4_allF_match_iff_weight_eq μ hpos hμ1 σ ν

/--
[oc4_fk_no_product_weight_expectAsCubeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_fk_no_product_weight_expectAsCubeAt_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {e e' : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (he : e ≠ e')
  (hfkg : Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0) :
-- imply
  ¬ ∃ ν : Sym2 V → Bool → ℝ, IsProbWeight ν ∧ ∀ f, oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f := by
-- proof
  apply StatMech.Walls.oc4_fk_no_product_weight_expectAsCubeAt G hp hp1 hq σ e e' he hfkg

/--
[oc4_fk_allF_match_forces_uncorrelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_fk_allF_match_forces_uncorrelated_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {ν : Sym2 V → Bool → ℝ}
  {e e' : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hν : IsProbWeight ν)
  (hall : ∀ f, oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f)
  (he : e ≠ e') :
-- imply
  Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') = 0 := by
-- proof
  apply StatMech.Walls.oc4_fk_allF_match_forces_uncorrelated G hp hp1 hq σ hν hall e e' he

/--
[oc4_posCorrMu_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_posCorrMu_pos_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∀ ω, 0 < oc4_posCorrMu ω := by
-- proof
  apply StatMech.Walls.oc4_posCorrMu_pos

/--
[oc4_posCorrMu_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_posCorrMu_sum_eq_one_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∑ ω : ConfigSpace (Fin 2), oc4_posCorrMu ω = 1 := by
-- proof
  apply StatMech.Walls.oc4_posCorrMu_sum_eq_one

/--
[oc4_posCorrMu_cov_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_posCorrMu_cov_ne_zero_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  Lindeberg.cov oc4_posCorrMu (Lindeberg.coord (0 : Fin 2)) (Lindeberg.coord (1 : Fin 2)) ≠ 0 := by
-- proof
  apply StatMech.Walls.oc4_posCorrMu_cov_ne_zero

/--
[oc4_posCorrMu_genuinelyCorrelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_posCorrMu_genuinelyCorrelated_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  oc3_GenuinelyCorrelated oc4_posCorrMu := by
-- proof
  apply StatMech.Walls.oc4_posCorrMu_genuinelyCorrelated

/--
[oc4_no_product_weight_expectAsCubeAt_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean)
-/
@[path]
private lemma oc4_no_product_weight_expectAsCubeAt_witness_eq
  [Fintype E]
  [DecidableEq E]
  {σ : Fin 2 ≃ Fin 2} :
-- imply
  ¬ ∃ ν : Fin 2 → Bool → ℝ, IsProbWeight ν ∧ ∀ f, oc2_ExpectAsCubeAt ν oc4_posCorrMu (σ : Fin 2 → Fin 2) f := by
-- proof
  apply StatMech.Walls.oc4_no_product_weight_expectAsCubeAt_witness σ


-- created on 2026-10-23
