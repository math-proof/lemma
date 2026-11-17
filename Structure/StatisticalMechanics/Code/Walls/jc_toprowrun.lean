/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Walls.jc_toprowrun.Part3
public section

open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


structure jc_TopRowRun (K : Set (Site 2)) (c : Site 2) (L : ℕ) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  run_mem : ∀ j : ℕ, j ≤ L → jc_shiftX c (j : ℤ) ∈ K
  
  run_maximal : jc_shiftX c ((L : ℤ) + 1) ∉ K
  
  run_topRow : ∀ j : ℕ, (jc_shiftX c (j : ℤ)) 1 = c 1
  
  topRow_maximal : ∀ v ∈ K, v 1 ≤ c 1
  
  leftMost : jc_shiftX c (-1) ∉ K


end Walls
end StatMech
