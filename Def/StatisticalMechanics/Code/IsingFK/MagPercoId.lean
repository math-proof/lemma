/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoId.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionRegime
open MeasureTheory Filter Topology


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK

variable {d : ℕ}


noncomputable def boundaryConnProfile (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (n : ℕ) : ℝ :=
  fkBoundaryConnReal d hp hp1 hq n


end IsingFK
end StatMech
