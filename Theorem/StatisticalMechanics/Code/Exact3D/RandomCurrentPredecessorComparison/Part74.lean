/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part13
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorCurrentSumComparisonAt_of_rows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T : OrderedWedgeStrictSectorYPredecessorCurrentSumRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorCurrentSumComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  let p :
      {u : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n u ∧
          ((u : Lattice.Site 3) (1 : Fin 3)) <
            ((u : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((u : Lattice.Site 3) (1 : Fin 3))} :=
    ⟨v, hvwedge, hlt, hypos⟩
  exact T.sound p (hrows (T.classify p) (T.covers p))


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_rows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T : OrderedWedgePredecessorCurrentSumRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hvwedge hlt
    let p :
        {u : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n u ∧
            ((u : Lattice.Site 3) (1 : Fin 3)) <
              ((u : Lattice.Site 3) (2 : Fin 3))} :=
      ⟨v, hvwedge, hlt⟩
    exact T.soundStrictZ p (hrows (T.classifyStrictZ p) (T.coversStrictZ p))
  · intro v hvwedge hheight hnotlt
    let p :
        {u : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n u ∧
            boxVertTransverseHeight3 u ≠ 0 ∧
              ¬ ((u : Lattice.Site 3) (1 : Fin 3)) <
                ((u : Lattice.Site 3) (2 : Fin 3))} :=
      ⟨v, hvwedge, hheight, hnotlt⟩
    exact T.soundDiagY p (hrows (T.classifyDiagY p) (T.coversDiagY p))
  · intro v hvwedge hlt hypos
    let p :
        {u : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n u ∧
            ((u : Lattice.Site 3) (1 : Fin 3)) <
              ((u : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((u : Lattice.Site 3) (1 : Fin 3))} :=
      ⟨v, hvwedge, hlt, hypos⟩
    exact T.soundStrictY p (hrows (T.classifyStrictY p) (T.coversStrictY p))


end Exact3D
end StatMech
