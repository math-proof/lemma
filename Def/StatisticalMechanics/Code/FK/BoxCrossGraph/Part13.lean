/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part12
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


noncomputable def innerFibreEquiv (d n : ℕ) :
    {ρ : ConfigSpace (Sym2 (boxVerts d (n+1))) //
        AgreesOff (innerEdgeFinset d n) (fun _ => false) ρ} ≃
      ConfigSpace (Sym2 (boxVerts d n)) where
  toFun ρ := innerRestrict d n ρ.1
  invFun ω := ⟨crossExt d n ω, agreesOff_crossExt d n ω⟩
  left_inv ρ := by
    apply Subtype.ext
    exact crossExt_innerRestrict_of_agreesOff d n ρ.2
  right_inv ω := innerRestrict_crossExt d n ω


end FK
end StatMech
