import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc8munonneg
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc8_mu_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_mu_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {GΛ : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  {o x y g : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc8_mu_nonneg GΛ β h hβ hh o x y g

/--
[gc8_magY_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_magY_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {GΛ : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  {y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation GΛ β h (spinProd ({y} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc8_magY_nonneg GΛ β h hβ hh y

/--
[gc8_magYsq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_magYsq_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {GΛ : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  {y : V}
-- given
  (β h : ℝ) :
-- imply
  0 ≤ (isingExpectation GΛ β h (spinProd ({y} : Finset V))) ^ 2 := by
-- proof
  apply StatMech.Walls.gc8_magYsq_nonneg GΛ β h y

/--
[gc8_twoPoint_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_twoPoint_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {o x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation GS β h (spinProd ({o, x} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc8_twoPoint_nonneg GS β h hβ hh o x

/--
[gc8_normaliser_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_normaliser_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {GΛ GS : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  [DecidableRel GS.Adj]
  {o x y g : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) * (isingExpectation GΛ β h (spinProd ({y} : Finset V))) ^ 2 * isingExpectation GS β h (spinProd ({o, x} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc8_normaliser_nonneg GΛ GS β h hβ hh o x y g

/--
[gc8_claim1_griffiths_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_claim1_griffiths_step_eq
  [Fintype V]
  [DecidableEq V]
  {GΛ GS : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  [DecidableRel GS.Adj]
  {o x y g : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hgriff : isingExpectation GS β h (spinProd ({y} : Finset V)) ≤ isingExpectation GΛ β h (spinProd ({y} : Finset V))) :
-- imply
  isingExpectation GΛ β h (spinProd ({y} : Finset V)) * (isingExpectation GS β h (spinProd ({y} : Finset V)) * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V))) ≥ (isingExpectation GS β h (spinProd ({y} : Finset V))) ^ 2 * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc8_claim1_griffiths_step GΛ GS β h hβ hh o x y g hgriff

/--
[gc8_claim1_normaliser_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_claim1_normaliser_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {GΛ GS : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  [DecidableRel GS.Adj]
  {o x y g : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hgriff : isingExpectation GS β h (spinProd ({y} : Finset V)) ≤ isingExpectation GΛ β h (spinProd ({y} : Finset V))) :
-- imply
  isingExpectation GS β h (spinProd ({o, x} : Finset V)) * (isingExpectation GΛ β h (spinProd ({y} : Finset V)) * (isingExpectation GS β h (spinProd ({y} : Finset V)) * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)))) ≥ isingExpectation GS β h (spinProd ({o, x} : Finset V)) * ((isingExpectation GS β h (spinProd ({y} : Finset V))) ^ 2 * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V))) := by
-- proof
  apply StatMech.Walls.gc8_claim1_normaliser_lower_bound GΛ GS β h hβ hh o x y g hgriff

/--
[gc8_twoPoint_ge_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_twoPoint_ge_product_eq
  [Fintype V]
  [DecidableEq V]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {o x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x) :
-- imply
  isingExpectation GS β h (spinProd ({o} : Finset V)) * isingExpectation GS β h (spinProd ({x} : Finset V)) ≤ isingExpectation GS β h (spinProd ({o, x} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc8_twoPoint_ge_product GS β h hβ hh o x hox

/--
[gc8_mu_clause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_mu_clause_eq
  [Fintype V]
  [DecidableEq V]
  {GΛ : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  {o x y g : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  ∃ μ : ℝ, 0 ≤ μ ∧ μ = isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc8_mu_clause GΛ β h hβ hh o x y g

/--
[gc8_mu_nonneg_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_mu_nonneg_nonvacuous_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2} : Finset (Fin 3))) := by
-- proof
  apply StatMech.Walls.gc8_mu_nonneg_nonvacuous

/--
[gc8_normaliser_nonneg_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8munonneg.lean)
-/
@[path]
private lemma gc8_normaliser_nonneg_nonvacuous_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2, 0} : Finset (Fin 3))) * (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({2} : Finset (Fin 3)))) ^ 2 * isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) := by
-- proof
  apply StatMech.Walls.gc8_normaliser_nonneg_nonvacuous


-- created on 2026-10-23
