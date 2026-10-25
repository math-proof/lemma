/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.Peierls.Part3
open MeasureTheory Filter Topology Finset
open scoped BigOperators ENNReal


set_option linter.unusedVariables false

set_option linter.style.show false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def fvMagOrigin (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : ℝ :=
  ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ * spin (glue η τ) (origin d)


end Ising
end StatMech
