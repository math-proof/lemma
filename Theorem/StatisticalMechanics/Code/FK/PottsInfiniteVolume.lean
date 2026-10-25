/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


theorem probabilityMeasure_seq_compact
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [SecondCountableTopology X] [T2Space X]
    (mu : ℕ → ProbabilityMeasure X) :
    ∃ (nu : ProbabilityMeasure X) (phi : ℕ → ℕ), StrictMono phi ∧
      Tendsto (mu ∘ phi) atTop (nhds nu) := by
  obtain ⟨nu, phi, hphi, hlim⟩ := CompactSpace.tendsto_subseq mu
  exact ⟨nu, phi, hphi, hlim⟩


end FK
end StatMech
