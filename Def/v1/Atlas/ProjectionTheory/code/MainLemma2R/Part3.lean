/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Instance.v1.Atlas.ProjectionTheory.code.MainLemma2R


noncomputable section

open MeasureTheory Metric Set Finset

open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- The aggregated tube sum $f(x) = \sum_i \psi_i(x)$. -/
def TubeCollection.tubeSum (S : TubeCollection) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i : S.ι, S.ψ i x

/-- The number of tubes in `S` contained in the $r \times R$ rectangle with center `c`
and direction `d`. -/
def TubeCollection.countContained (S : TubeCollection) (r : ℝ)
    (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (Finset.univ.filter fun j =>
    (S.tubes j).asSet ⊆ rectangleSet c d r S.R).card

/-- The multiplicity at scale $r$: the maximum, over all $r \times R$ rectangles, of the
number of tubes of `S` contained in that rectangle. -/
def TubeCollection.multiplicity (S : TubeCollection) (r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)),
    n = S.countContained r c d}

end ProjectionTheory
end
