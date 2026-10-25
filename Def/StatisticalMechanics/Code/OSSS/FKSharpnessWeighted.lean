/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part5
open scoped BigOperators
open Finset Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeighted

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential WiredBoxDifferential

open ActiveEdgeDifferential

open FK RevealmentTranslation


noncomputable def weightedWiredActiveTheta
    (d n : ℕ) (J : Sym2 (boxVerts d n) → ℝ) (q beta : ℝ) : ℝ :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
      (FK.betaParams J beta) q)
    (crossIndG (boxActiveEdge d n) 0 n)


noncomputable def weightedWiredActiveDenom
    (d n : ℕ) (J : Sym2 (boxVerts d n) → ℝ) (q beta : ℝ) : ℝ := by
  classical
  exact 4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
      (fun x => ∑ j ∈ Finset.range n,
        Lindeberg.mean
          (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (FK.betaParams J beta) q)
          (fun omega => if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x j)
            then (1 : ℝ) else 0)) / (n : ℝ)


end FKSharpnessWeighted
end OSSS
end StatMech
