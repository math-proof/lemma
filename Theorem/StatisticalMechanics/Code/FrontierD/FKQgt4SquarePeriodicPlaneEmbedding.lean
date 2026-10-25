/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar

noncomputable section

@[simp] theorem squareComplexPoint_re (x : Site 2) :
    (squareComplexPoint x).re = x 0 := by
  simp [squareComplexPoint]

@[simp] theorem squareComplexPoint_im (x : Site 2) :
    (squareComplexPoint x).im = x 1 := by
  simp [squareComplexPoint]

theorem squareComplexPoint_injective : Function.Injective squareComplexPoint := by
  intro x y hxy
  apply funext
  intro i
  fin_cases i
  · have h0 := congrArg Complex.re hxy
    have h0' : ((x 0 : Int) : Real) = (y 0 : Int) := by
      simpa only [squareComplexPoint_re] using h0
    exact_mod_cast h0'
  · have h1 := congrArg Complex.im hxy
    have h1' : ((x 1 : Int) : Real) = (y 1 : Int) := by
      simpa only [squareComplexPoint_im] using h1
    exact_mod_cast h1'


end
end StatMech.FrontierD
