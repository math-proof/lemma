import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[ssl_summable_classTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_summable_classTerm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {sel : (↥G.edgeFinset → ℕ) → ι}
  {i : ι} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => if sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i then weight G β J (ofEdgeFun G m) else 0) := by
-- proof
  apply StatMech.Sharpness.ssl_summable_classTerm G β J x y sel i

/--
[ssl_sum_backboneClassSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_sum_backboneClassSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  [Fintype ι]
  {sel : (↥G.edgeFinset → ℕ) → ι} :
-- imply
  ∑ i : ι, ssl_backboneClassSum G β J x y sel i = currentSum G β J {x, y} := by
-- proof
  apply StatMech.Sharpness.ssl_sum_backboneClassSum G β J x y sel

/--
[ssl_P1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_P1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  [Fintype ι]
  {sel : (↥G.edgeFinset → ℕ) → ι} :
-- imply
  expectationJ G β J {x, y} = ∑ i : ι, ssl_backboneWeight G β J x y sel i := by
-- proof
  apply StatMech.Sharpness.ssl_P1 G β J x y sel

/--
[ssl_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_weight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n : Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weight G β J n := by
-- proof
  apply StatMech.Sharpness.ssl_weight_nonneg G β J hβ hJ n

/--
[ssl_currentSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_currentSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ currentSum G β J A := by
-- proof
  apply StatMech.Sharpness.ssl_currentSum_nonneg G β J hβ hJ A

/--
[ssl_expectationJ_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_expectationJ_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ expectationJ G β J A := by
-- proof
  apply StatMech.Sharpness.ssl_expectationJ_nonneg G β J hβ hJ A

/--
[ssl_backboneWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_backboneWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {sel : (↥G.edgeFinset → ℕ) → ι}
  {i : ι}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ ssl_backboneWeight G β J x y sel i := by
-- proof
  apply StatMech.Sharpness.ssl_backboneWeight_nonneg G β J x y hβ hJ sel i

/--
[ssl_sum_prod_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_sum_prod_restrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S T : Finset V}
  {f : V → V → ℝ} :
-- imply
  ∑ p : V × V, (if p.1 ∈ S ∧ p.2 ∈ T then f p.1 p.2 else 0) = ∑ x ∈ S, ∑ y ∈ T, f x y := by
-- proof
  apply StatMech.Sharpness.ssl_sum_prod_restrict G S T f

/--
[ssl_simon_at_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_simon_at_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o : V}
  {boundaryTargets : Finset V}
  {z : V}
  {selFE : (↥G.edgeFinset → ℕ) → V × V}
-- given
  (hFE_bound : ∀ x ∈ S, ∀ y ∈ boundaryTargets, ssl_backboneWeight G β J o z selFE (x, y) ≤ simonWeight G β J S o x y * expectationJ G β J {y, z})
  (hFE_zero : ∀ p : V × V, ¬ (p.1 ∈ S ∧ p.2 ∈ boundaryTargets) → ssl_backboneWeight G β J o z selFE p ≤ 0) :
-- imply
  expectationJ G β J {o, z} ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simonWeight G β J S o x y * expectationJ G β J {y, z} := by
-- proof
  apply StatMech.Sharpness.ssl_simon_at_target G β J S o boundaryTargets z selFE hFE_bound hFE_zero

/--
[ssl_simonLieb_of_firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_simonLieb_of_firstExit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o : V}
  {boundaryTargets : Finset V}
  {selFE : V → (↥G.edgeFinset → ℕ) → V × V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x})
  (hFE_bound : ∀ z, z ∉ S → ∀ x ∈ S, ∀ y ∈ boundaryTargets, ssl_backboneWeight G β J o z (selFE z) (x, y) ≤ simonWeight G β J S o x y * expectationJ G β J {y, z})
  (hFE_zero : ∀ z, z ∉ S → ∀ p : V × V, ¬ (p.1 ∈ S ∧ p.2 ∈ boundaryTargets) → ssl_backboneWeight G β J o z (selFE z) p ≤ 0) :
-- imply
  SimonLieb (fun a b => expectationJ G β J {a, b}) o S (simonWeight G β J S o) boundaryTargets := by
-- proof
  apply StatMech.Sharpness.ssl_simonLieb_of_firstExit G β J S o boundaryTargets hβ hJ hcorr selFE hFE_bound hFE_zero

/--
[ssl_finite_susceptibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean)
-/
@[path]
private lemma ssl_finite_susceptibility_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o : V}
  {boundaryTargets : Finset V}
  {Λ W : Finset V}
-- given
  (hSL : SimonLieb (fun a b => expectationJ G β J {a, b}) o S (simonWeight G β J S o) boundaryTargets)
  (hφ1 : simonConst S (simonWeight G β J S o) boundaryTargets < 1)
  (hχbarW : ∀ y ∈ boundaryTargets, ∑ z ∈ W \ S, expectationJ G β J {y, z} ≤ ∑ z ∈ W, expectationJ G β J {o, z})
  (hSboundW : ∑ z ∈ W ∩ S, expectationJ G β J {o, z} ≤ (S.card : ℝ))
  (hΛbar : ∑ z ∈ Λ, expectationJ G β J {o, z} ≤ ∑ z ∈ W, expectationJ G β J {o, z}) :
-- imply
  ∑ z ∈ Λ, expectationJ G β J {o, z} ≤ (S.card : ℝ) / (1 - simonConst S (simonWeight G β J S o) boundaryTargets) := by
-- proof
  apply StatMech.Sharpness.ssl_finite_susceptibility G β J S o boundaryTargets hSL hφ1 Λ W hχbarW hSboundW hΛbar


-- created on 2026-10-23
