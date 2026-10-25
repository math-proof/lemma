import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc9betaderivcov3
open Finset SimpleGraph StatMech StatMech.Walls


/--
[gc9_beta_deriv_cov3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9betaderivcov3.lean)
-/
@[path]
private lemma gc9_beta_deriv_cov3_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun β => isingExpectation G β h (fun s => spin s o)) β = bondEnergySusceptibility G β h o + h * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc9_beta_deriv_cov3 G β h o

/--
[gc9_beta_deriv_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9betaderivcov3.lean)
-/
@[path]
private lemma gc9_beta_deriv_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingExpectation G β h (fun s => spin s o)) (bondEnergySusceptibility G β h o + h * susceptibility G β h o) β := by
-- proof
  apply StatMech.Walls.gc9_beta_deriv_hasDerivAt G β h o

/--
[gc9_beta_deriv_book_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9betaderivcov3.lean)
-/
@[path]
private lemma gc9_beta_deriv_book_form_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun β => isingExpectation G β h (fun s => spin s o)) β = (∑ e ∈ G.edgeFinset, (isingExpectation G β h (fun s => spin s o * bond s e) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => bond s e))) + h * ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) := by
-- proof
  apply StatMech.Walls.gc9_beta_deriv_book_form G β h o

/--
[gc9_field_term_eq_fieldFluct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9betaderivcov3.lean)
-/
@[path]
private lemma gc9_field_term_eq_fieldFluct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : β ≠ 0) :
-- imply
  h * susceptibility G β h o = (h / β) * deriv (fun h => isingExpectation G β h (fun s => spin s o)) h := by
-- proof
  apply StatMech.Walls.gc9_field_term_eq_fieldFluct G β h hβ o

/--
[gc9_beta_deriv_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9betaderivcov3.lean)
-/
@[path]
private lemma gc9_beta_deriv_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  deriv (fun β => isingExpectation (⊤ : SimpleGraph (Fin 2)) β h (fun s => spin s 0)) β = bondEnergySusceptibility (⊤ : SimpleGraph (Fin 2)) β h 0 + h * susceptibility (⊤ : SimpleGraph (Fin 2)) β h 0 := by
-- proof
  apply StatMech.Walls.gc9_beta_deriv_nonvacuous G β h


-- created on 2026-10-23
