/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

noncomputable def isingTorusIndexedEdgeEquiv :
    IsingDyadicTorus d k × Fin d ≃ (isingTorusGraph d k).edgeFinset :=
  Equiv.ofBijective
    (fun p => ⟨isingTorusIndexedEdge p,
      isingTorusIndexedEdge_mem_edgeFinset p⟩)
    ⟨fun _ _ h => isingTorusIndexedEdge_injective (Subtype.ext_iff.mp h),
      isingTorusIndexedEdge_surjective⟩

end StatMech.FrontierA
