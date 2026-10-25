/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.KestenHalf
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
open MeasureTheory Set Filter Topology SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


noncomputable def kdi_rotEdgeEquiv : Sym2 (Site 2) ≃ Sym2 (Site 2) := sym2Congr rot90Equiv


noncomputable def kdi_rotConfig :
    ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) kdi_rotEdgeEquiv


end TwoDim
end StatMech
