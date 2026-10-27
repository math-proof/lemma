import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc3_noproductweight.Part3
open Finset StatMech StatMech.Walls


/--
[oc3_weight_eq_of_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_weight_eq_of_match_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ}
  {ω₀ : ConfigSpace E}
-- given
  (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g) :
-- imply
  weight ν ω₀ = μ ω₀ := by
-- proof
  apply StatMech.Walls.oc3_weight_eq_of_match hmatch ω₀

/--
[oc3_cov_eq_of_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_cov_eq_of_match_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ}
  {F G : ConfigSpace E → ℝ}
-- given
  (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g) :
-- imply
  cov ν F G = Lindeberg.cov μ F G := by
-- proof
  apply StatMech.Walls.oc3_cov_eq_of_match hmatch F G

/--
[oc3_coordI_flipAt_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_coordI_flipAt_ne_eq
  [Fintype E]
  [DecidableEq E]
  {e e' : E}
  {ω : ConfigSpace E}
-- given
  (he : e ≠ e') :
-- imply
  coordI e' (flipAt e ω) = coordI e' ω := by
-- proof
  apply StatMech.Walls.oc3_coordI_flipAt_ne e e' he ω

/--
[oc3_cov_coordI_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_cov_coordI_cross_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e e' : E}
-- given
  (hν : IsProbWeight ν)
  (he : e ≠ e') :
-- imply
  cov ν (coordI e) (coordI e') = 0 := by
-- proof
  apply StatMech.Walls.oc3_cov_coordI_cross hν e e' he

/--
[oc3_no_product_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_no_product_weight_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
-- given
  (hcorr : oc3_GenuinelyCorrelated μ) :
-- imply
  ¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧ ∀ g, expect ν g = Lindeberg.mean μ g := by
-- proof
  apply StatMech.Walls.oc3_no_product_weight hcorr

/--
[oc3_match_forces_uncorrelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_match_forces_uncorrelated_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ}
  {e e' : E}
-- given
  (hν : IsProbWeight ν)
  (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g)
  (he : e ≠ e') :
-- imply
  Lindeberg.cov μ (Lindeberg.coord e) (Lindeberg.coord e') = 0 := by
-- proof
  apply StatMech.Walls.oc3_match_forces_uncorrelated hν hmatch e e' he

/--
[oc3_match_iff_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_match_iff_weight_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ} :
-- imply
  (∀ g, expect ν g = Lindeberg.mean μ g) ↔ (∀ ω, weight ν ω = μ ω) := by
-- proof
  apply StatMech.Walls.oc3_match_iff_weight_eq

/--
[oc3_match_forces_revealment_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_match_forces_revealment_one_eq
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
  apply StatMech.Walls.oc3_match_forces_revealment_one hpos hμ1 σ f e₀ he₀ hnc T hmatch

/--
[oc3_corrMu_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_corrMu_sum_eq_one_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∑ ω : ConfigSpace (Fin 2), oc3_corrMu ω = 1 := by
-- proof
  apply StatMech.Walls.oc3_corrMu_sum_eq_one

/--
[oc3_corrMu_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_corrMu_nonneg_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∀ ω, 0 ≤ oc3_corrMu ω := by
-- proof
  apply StatMech.Walls.oc3_corrMu_nonneg

/--
[oc3_corrMu_cov_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_corrMu_cov_ne_zero_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  Lindeberg.cov oc3_corrMu (Lindeberg.coord (0 : Fin 2)) (Lindeberg.coord (1 : Fin 2)) ≠ 0 := by
-- proof
  apply StatMech.Walls.oc3_corrMu_cov_ne_zero

/--
[oc3_corrMu_genuinelyCorrelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_corrMu_genuinelyCorrelated_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  oc3_GenuinelyCorrelated oc3_corrMu := by
-- proof
  apply StatMech.Walls.oc3_corrMu_genuinelyCorrelated

/--
[oc3_no_product_weight_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_no_product_weight_witness_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ¬ ∃ ν : Fin 2 → Bool → ℝ, IsProbWeight ν ∧ ∀ g, expect ν g = Lindeberg.mean oc3_corrMu g := by
-- proof
  apply StatMech.Walls.oc3_no_product_weight_witness

/--
[oc3_fk_no_product_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean)
-/
@[path]
private lemma oc3_fk_no_product_weight_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e e' : Sym2 V}
-- given
  (he : e ≠ e')
  (hcorr : Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0) :
-- imply
  ¬ ∃ ν : Sym2 V → Bool → ℝ, IsProbWeight ν ∧ ∀ g, expect ν g = Lindeberg.mean (fkMass G p q) g := by
-- proof
  apply StatMech.Walls.oc3_fk_no_product_weight G p q e e' he hcorr


-- created on 2026-10-23
