/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DobrushinStateProfileLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
open MeasureTheory Filter Topology


namespace StatMech.Ising

open StatMech.Lattice

noncomputable section

variable {d : Nat}


def interfaceMeasure (i : Fin d) (n : Nat) (beta : Real) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (interfaceField i) n (bondFinsetTouch d n) beta 0


def interfaceState (i : Fin d) (beta : Real) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => interfaceMeasure i n beta)

end
end StatMech.Ising
