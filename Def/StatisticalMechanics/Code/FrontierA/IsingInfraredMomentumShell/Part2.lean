/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredMomentumShell
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open Lattice


noncomputable def integerMomentumBoxWithoutZero (d M : Nat) :
    Finset (Site d) :=
  boxSV_boxF d M \ {0}

end StatMech.FrontierA
