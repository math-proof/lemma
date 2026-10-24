import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc10eq15
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc10_eq15_sourceRemoval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_eq15_sourceRemoval_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  Sharpness.currentSum G β J A = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc10_eq15_sourceRemoval G β J A

/--
[gc10_eq15_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_eq15_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A : Finset (Option V)} :
-- imply
  Sharpness.currentSum (withGhost G) β J A = Sharpness.expectationJ (withGhost G) β J A * Sharpness.currentSum (withGhost G) β J ∅ := by
-- proof
  apply StatMech.Walls.gc10_eq15_ghost G β J A

/--
[gc10_currentMass_product_eq_sourcePairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_currentMass_product_eq_sourcePairSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A B : Finset (Option V)} :
-- imply
  Sharpness.currentSum (withGhost G) β J A * Sharpness.currentSum (withGhost G) β J B = Sharpness.sourcePairSum (withGhost G) β J A B := by
-- proof
  apply StatMech.Walls.gc10_currentMass_product_eq_sourcePairSum G β J A B

/--
[gc10_eq15_product_two_currentMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_eq15_product_two_currentMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A B : Finset (Option V)} :
-- imply
  (Sharpness.expectationJ (withGhost G) β J A * Sharpness.expectationJ (withGhost G) β J B) * (Sharpness.currentSum (withGhost G) β J ∅) ^ 2 = Sharpness.currentSum (withGhost G) β J A * Sharpness.currentSum (withGhost G) β J B := by
-- proof
  apply StatMech.Walls.gc10_eq15_product_two_currentMass G β J A B

/--
[gc10_correlationProduct_eq_sourcePairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_correlationProduct_eq_sourcePairSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A B : Finset (Option V)} :
-- imply
  (Sharpness.expectationJ (withGhost G) β J A * Sharpness.expectationJ (withGhost G) β J B) * (Sharpness.currentSum (withGhost G) β J ∅) ^ 2 = Sharpness.sourcePairSum (withGhost G) β J A B := by
-- proof
  apply StatMech.Walls.gc10_correlationProduct_eq_sourcePairSum G β J A B

/--
[gc10_sourcePairSum_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_sourcePairSum_superposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A B : Finset (Option V)} :
-- imply
  Sharpness.sourcePairSum (withGhost G) β J A B = ∑' m : ↥(withGhost G).edgeFinset → ℕ, ∑ K : {p : ↥(withGhost G).edgeFinset → ℕ // p ≤ m}, (if sources (withGhost G) (ofEdgeFun (withGhost G) K.1) = A then weight (withGhost G) β J (ofEdgeFun (withGhost G) K.1) else 0) * (if sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K.1 e)) = B then weight (withGhost G) β J (ofEdgeFun (withGhost G) (fun e => m e - K.1 e)) else 0) := by
-- proof
  apply StatMech.Walls.gc10_sourcePairSum_superposition G β J A B

/--
[gc10_eq15_currentMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_eq15_currentMass_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  0 < Sharpness.currentSum (withGhost G) β J ∅ := by
-- proof
  apply StatMech.Walls.gc10_eq15_currentMass_pos G β J

/--
[gc10_eq15_currentMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_eq15_currentMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A : Finset (Option V)}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.currentSum (withGhost G) β J A ∧ 0 ≤ Sharpness.expectationJ (withGhost G) β J A := by
-- proof
  apply StatMech.Walls.gc10_eq15_currentMass_nonneg G β J hβ hJ A

/--
[gc10_eq15_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_eq15_magnetization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
-- given
  (β h : ℝ) :
-- imply
  Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) = isingExpectation G β h (fun s => spin s y) * Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc10_eq15_magnetization G β h y

/--
[gc10_eq15_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10eq15.lean)
-/
@[path]
private lemma gc10_eq15_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
  {J : Sym2 (Option (Fin 4)) → ℝ} :
-- imply
  (Sharpness.expectationJ (withGhost (⊥ : SimpleGraph (Fin 4))) β J ({some 1, some 2} : Finset (Option (Fin 4))) * Sharpness.expectationJ (withGhost (⊥ : SimpleGraph (Fin 4))) β J ({some 3, none} : Finset (Option (Fin 4)))) * (Sharpness.currentSum (withGhost (⊥ : SimpleGraph (Fin 4))) β J ∅) ^ 2 = Sharpness.sourcePairSum (withGhost (⊥ : SimpleGraph (Fin 4))) β J ({some 1, some 2} : Finset (Option (Fin 4))) ({some 3, none} : Finset (Option (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc10_eq15_nonvacuous β J


-- created on 2026-10-23
