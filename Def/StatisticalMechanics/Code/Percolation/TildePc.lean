/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
open MeasureTheory
open scoped NNReal
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def coordShift (x : Site d) (i : Fin d) (δ : ℤ) : Site d :=
  Function.update x i (x i + δ)


def stepSign (b : Bool) : ℤ := if b then 1 else -1


noncomputable def boundaryEdges (d : ℕ) (S : Finset (Site d)) :
    Finset (Site d × Site d) := by
  classical
  exact
    ((S ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset Bool)).filter
        (fun t => coordShift t.1 t.2.1 (stepSign t.2.2) ∉ S)).image
      (fun t => (t.1, coordShift t.1 t.2.1 (stepSign t.2.2)))


noncomputable def connWithinProb (d : ℕ) (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d))
    (x : Site d) : ℝ := by
  classical
  exact
    if h0 : origin d ∈ S then
      if hx : x ∈ S then
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          {ω | ConnectedWithin d ω (S : Set (Site d)) ⟨origin d, h0⟩ ⟨x, hx⟩}
      else 0
    else 0


end Percolation
end StatMech
