import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.GKS2
open Finset StatMech StatMech.Ising


/--
[spinProd_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma spinProd_mul_self_eq
  [Fintype V]
  [DecidableEq V]
  {A B : Finset V}
  {s : ConfigSpace V} :
-- imply
  spinProd A s * spinProd B s = spinProd (A ∆ B) s := by
-- proof
  apply StatMech.Ising.spinProd_mul_self A B s

/--
[spin_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma spin_xnor_eq
  [Fintype V]
  [DecidableEq V]
  {σ q : ConfigSpace V}
  {x : V} :
-- imply
  spin (xnor σ q) x = spin σ x * spin q x := by
-- proof
  apply StatMech.Ising.spin_xnor σ q x

/--
[bond_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma bond_xnor_eq
  [Fintype V]
  [DecidableEq V]
  {σ q : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond (xnor σ q) e = bond σ e * bond q e := by
-- proof
  apply StatMech.Ising.bond_xnor σ q e

/--
[spinProd_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma spinProd_xnor_eq
  [Fintype V]
  [DecidableEq V]
  {B : Finset V}
  {σ q : ConfigSpace V} :
-- imply
  spinProd B (xnor σ q) = spinProd B σ * spinProd B q := by
-- proof
  apply StatMech.Ising.spinProd_xnor B σ q

/--
[dblFun_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma dblFun_invol_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  Function.Involutive (dblFun (V := V)) := by
-- proof
  apply StatMech.Ising.dblFun_invol

/--
[sum_dbl_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma sum_dbl_reindex_eq
  [Fintype V]
  [DecidableEq V]
  {F : ConfigSpace V × ConfigSpace V → ℝ} :
-- imply
  ∑ p : ConfigSpace V × ConfigSpace V, F p = ∑ p : ConfigSpace V × ConfigSpace V, F (p.1, xnor p.1 p.2) := by
-- proof
  apply StatMech.Ising.sum_dbl_reindex F

/--
[one_add_bond_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma one_add_bond_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  0 ≤ 1 + bond q e := by
-- proof
  apply StatMech.Ising.one_add_bond_nonneg q e

/--
[one_add_spin_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma one_add_spin_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {x : V} :
-- imply
  0 ≤ 1 + spin q x := by
-- proof
  apply StatMech.Ising.one_add_spin_nonneg q x

/--
[one_sub_spinProd_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma one_sub_spinProd_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {B : Finset V}
  {q : ConfigSpace V} :
-- imply
  0 ≤ 1 - spinProd B q := by
-- proof
  apply StatMech.Ising.one_sub_spinProd_nonneg B q

/--
[inner_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma inner_sum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ce de : Sym2 V → ℝ}
  {cx dx : V → ℝ}
  {obs : ConfigSpace V → ℝ}
-- given
  (hce : ∀ e, 0 ≤ ce e)
  (hde : ∀ e, 0 ≤ de e)
  (hcx : ∀ x, 0 ≤ cx x)
  (hdx : ∀ x, 0 ≤ dx x)
  (hobs : IsSpinMonomial obs) :
-- imply
  0 ≤ ∑ s : ConfigSpace V, obs s * ((∏ e ∈ G.edgeFinset, (ce e + bond s e * de e)) * (∏ x : V, (cx x + spin s x * dx x))) := by
-- proof
  apply StatMech.Ising.inner_sum_nonneg G ce de cx dx hce hde hcx hdx obs hobs

/--
[doubled_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma doubled_weight_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ q : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  isingWeight G β h σ * isingWeight G β h (xnor σ q) = (∏ e ∈ G.edgeFinset, (Real.cosh (β * (1 + bond q e)) + bond σ e * Real.sinh (β * (1 + bond q e)))) * (∏ x : V, (Real.cosh (β * h * (1 + spin q x)) + spin σ x * Real.sinh (β * h * (1 + spin q x)))) := by
-- proof
  apply StatMech.Ising.doubled_weight_factor G β h σ q

/--
[inner_q_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma inner_q_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
  {q : ConfigSpace V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ ∑ σ : ConfigSpace V, (spinProd (A ∆ B) σ * isingWeight G β h σ * isingWeight G β h (xnor σ q) - spinProd A σ * isingWeight G β h σ * (spinProd B (xnor σ q) * isingWeight G β h (xnor σ q))) := by
-- proof
  apply StatMech.Ising.inner_q_nonneg G β h hβ hh A B q

/--
[unnorm_gks2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma unnorm_gks2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, spinProd B s * isingWeight G β h s) ≤ (∑ s, spinProd (A ∆ B) s * isingWeight G β h s) * (∑ s, isingWeight G β h s) := by
-- proof
  apply StatMech.Ising.unnorm_gks2 G β h hβ hh A B

/--
[isingExpectation_spinProd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma isingExpectation_spinProd_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (spinProd A) = (∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s) / isingZ G β h := by
-- proof
  apply StatMech.Ising.isingExpectation_spinProd_eq G β h A

/--
[gks_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean)
-/
@[path]
private lemma gks_second_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  isingExpectation G β h (spinProd A) * isingExpectation G β h (spinProd B) ≤ isingExpectation G β h (spinProd (A ∆ B)) := by
-- proof
  apply StatMech.Ising.gks_second G β h hβ hh A B


-- created on 2026-10-23
