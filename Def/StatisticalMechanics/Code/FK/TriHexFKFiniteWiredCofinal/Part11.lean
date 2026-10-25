/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part11
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarTriBufferedOuterLevel (n : Nat) : Nat :=
  triangular.bufferedRadius (n + 1) + 1

def triHexPlanarTriBufferedToFiniteTerminal (n : Nat) :
    triangular.BufferedVertex n ↪
      TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n) where
  toFun v := ⟨v.1, by
    apply triangular_orbitBox_subset_triHexPlanarFiniteTerminal_succ
      (triangular.bufferedRadius (n + 1))
    exact triangular.orbitBox_mono
      (triangular.bufferedRadius_strictMono.monotone (Nat.le_succ n)) v.2⟩
  inj' _ _ h := Subtype.ext
    (congrArg (fun z : TriHexPlanarFiniteTerminal
      (triHexPlanarTriBufferedOuterLevel n) => z.1) h)

end
end StatMech.FK.PeriodicPlanar
