import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc6_mu_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_mu_nonneg_eq
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
  0 ≤ isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Walls.gc6_mu_nonneg G β h hβ hh A

/--
[gc6_ghostCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_ghostCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 (Option V)}
-- given
  (β h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ ghostCoupling h β (fun _ => 1) e := by
-- proof
  apply StatMech.Walls.gc6_ghostCoupling_nonneg G β h hh e

/--
[gc6_Z_B_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_Z_B_nonneg_eq
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
  0 ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb) := by
-- proof
  apply StatMech.Walls.gc6_Z_B_nonneg G β h hβ hh A

/--
[gc6_Z0_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_Z0_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc6_Z0_pos G β h

/--
[gc6_mu_eq_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_mu_eq_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Even A.card) :
-- imply
  isingExpectation G β h (spinProd A) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc6_mu_eq_ratio G β h A hA

/--
[gc6_mu_nonneg_of_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_mu_nonneg_of_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hA : Even A.card) :
-- imply
  0 ≤ isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Walls.gc6_mu_nonneg_of_ratio G β h hβ hh A hA

/--
[gc6_familyRealise_mu_clause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_familyRealise_mu_clause_eq
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
  ∃ μ : ℝ, 0 ≤ μ ∧ μ = isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Walls.gc6_familyRealise_mu_clause G β h hβ hh A

/--
[gc6_mu_nonneg_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_mu_nonneg_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) := by
-- proof
  apply StatMech.Walls.gc6_mu_nonneg_nonvacuous G

/--
[gc6_mu_eq_ratio_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_munonneg.lean)
-/
@[path]
private lemma gc6_mu_eq_ratio_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (({0, 1} : Finset (Fin 3)).map someEmb) / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc6_mu_eq_ratio_nonvacuous G


-- created on 2026-10-23
