import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
open StatMech StatMech.Universality


/--
[isingFiniteGraphDart_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphDart_card_le_eq
  [Fintype V]
  {G : SimpleGraph V}
  {D : Nat}
-- given
  (hdeg : ∀ x, Nat.card (G.neighborSet x) ≤ D) :
-- imply
  Nat.card G.Dart ≤ Fintype.card V * D := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDart_card_le G D hdeg

/--
[isingFiniteGraphDartFinset_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphDartFinset_card_le_eq
  [Fintype V]
  {G : SimpleGraph V}
  {D : Nat}
  {S : Finset G.Dart}
-- given
  (hdeg : ∀ x, Nat.card (G.neighborSet x) ≤ D) :
-- imply
  S.card ≤ Fintype.card V * D := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDartFinset_card_le G D hdeg S

/--
[isingFiniteGraphDartSum_cutoffEnergy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphDartSum_cutoffEnergy_le_eq
  [Fintype V]
  {G : SimpleGraph V}
  {eta : V → Real}
  {D : Nat}
  {L : Real}
-- given
  (hdeg : ∀ x, Nat.card (G.neighborSet x) ≤ D)
  (hL : 0 ≤ L)
  (hlip : ∀ d : G.Dart, |eta d.snd - eta d.fst| ≤ L) :
-- imply
  isingFiniteGraphDartSum G (fun x y ↦ (eta y - eta x) ^ 2) ≤ (Fintype.card V * D : Nat) * L ^ 2 := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDartSum_cutoffEnergy_le G eta D L hdeg hL hlip

/--
[fkIsingSquareRadialPatchPrimalNode_card_le_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCutoff.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalNode_card_le_sq_eq
  {m : Nat} :
-- imply
  Fintype.card (FKIsingSquareRadialPatchPrimalNode m) ≤ m ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalNode_card_le_sq m

/--
[fkIsingSquareRadialPatchDualNode_card_le_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCutoff.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualNode_card_le_sq_eq
  {m : Nat} :
-- imply
  Fintype.card (FKIsingSquareRadialPatchDualNode m) ≤ m ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualNode_card_le_sq m


-- created on 2026-10-23
