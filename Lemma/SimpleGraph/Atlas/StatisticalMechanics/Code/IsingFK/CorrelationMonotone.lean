import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.CorrelationMonotone
open Finset StatMech StatMech.IsingFK


/--
[weight_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma weight_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (h β₀ : ℝ) :
-- imply
  HasDerivAt (fun β => isingWeight G β h s) (energyObs G h s * isingWeight G β₀ h s) β₀ := by
-- proof
  apply StatMech.IsingFK.weight_hasDerivAt G h β₀ s

/--
[num_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma num_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (h β₀ : ℝ) :
-- imply
  HasDerivAt (fun β => ∑ s, spinProd A s * isingWeight G β h s) (∑ s, spinProd A s * (energyObs G h s * isingWeight G β₀ h s)) β₀ := by
-- proof
  apply StatMech.IsingFK.num_hasDerivAt G h β₀ A

/--
[den_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma den_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (h β₀ : ℝ) :
-- imply
  HasDerivAt (fun β => isingZ G β h) (∑ s, energyObs G h s * isingWeight G β₀ h s) β₀ := by
-- proof
  apply StatMech.IsingFK.den_hasDerivAt G h β₀

/--
[covar_spinProd_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma covar_spinProd_nonneg_eq
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
  0 ≤ (∑ s, (spinProd A s * spinProd B s) * isingWeight G β h s) * isingZ G β h - (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, spinProd B s * isingWeight G β h s) := by
-- proof
  apply StatMech.IsingFK.covar_spinProd_nonneg G β h hβ hh A B

/--
[covarTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma covarTerm_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {g : ConfigSpace V → ℝ}
  {B : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hgB : ∀ s, g s = spinProd B s) :
-- imply
  0 ≤ (∑ s, (spinProd A s * g s) * isingWeight G β h s) * isingZ G β h - (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, g s * isingWeight G β h s) := by
-- proof
  apply StatMech.IsingFK.covarTerm_nonneg G β h hβ hh A g B hgB

/--
[exists_spinProd_eq_bond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma exists_spinProd_eq_bond_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  ∃ B : Finset V, ∀ s : ConfigSpace V, bond s e = spinProd B s := by
-- proof
  apply StatMech.IsingFK.exists_spinProd_eq_bond G e he

/--
[spin_eq_spinProd_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma spin_eq_spinProd_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {s : ConfigSpace V} :
-- imply
  spin s x = spinProd {x} s := by
-- proof
  apply StatMech.IsingFK.spin_eq_spinProd_singleton G x s

/--
[num_deriv_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma num_deriv_decomp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ) :
-- imply
  (∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s)) = (∑ e ∈ G.edgeFinset, ∑ s, (spinProd A s * bond s e) * isingWeight G β h s) + h * ∑ x, ∑ s, (spinProd A s * spin s x) * isingWeight G β h s := by
-- proof
  apply StatMech.IsingFK.num_deriv_decomp G β h A

/--
[deriv_numerator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma deriv_numerator_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ (∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s)) * isingZ G β h - (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, energyObs G h s * isingWeight G β h s) := by
-- proof
  apply StatMech.IsingFK.deriv_numerator_nonneg G β h hβ hh A

/--
[corr_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma corr_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (h β₀ : ℝ) :
-- imply
  HasDerivAt (fun β => isingExpectation G β h (spinProd A)) (((∑ s, spinProd A s * (energyObs G h s * isingWeight G β₀ h s)) * isingZ G β₀ h - (∑ s, spinProd A s * isingWeight G β₀ h s) * (∑ s, energyObs G h s * isingWeight G β₀ h s)) / (isingZ G β₀ h) ^ 2) β₀ := by
-- proof
  apply StatMech.IsingFK.corr_hasDerivAt G h β₀ A

/--
[corr_deriv_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma corr_deriv_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (h β : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ ((∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s)) * isingZ G β h - (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, energyObs G h s * isingWeight G β h s)) / (isingZ G β h) ^ 2 := by
-- proof
  apply StatMech.IsingFK.corr_deriv_nonneg G h β hβ hh A

/--
[corr_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma corr_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  MonotoneOn (fun β => isingExpectation G β h (spinProd A)) (Set.Ici (0 : ℝ)) := by
-- proof
  apply StatMech.IsingFK.corr_monotone G h hh A

/--
[twoPoint_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma twoPoint_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  MonotoneOn (fun β => isingExpectation G β h (spinProd {x, y})) (Set.Ici (0 : ℝ)) := by
-- proof
  apply StatMech.IsingFK.twoPoint_monotone G h hh x y

/--
[magnetization_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean)
-/
@[path]
private lemma magnetization_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  MonotoneOn (fun β => isingExpectation G β h (spinProd {x})) (Set.Ici (0 : ℝ)) := by
-- proof
  apply StatMech.IsingFK.magnetization_monotone G h hh x


-- created on 2026-10-23
