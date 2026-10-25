/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part3
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

structure IsCompactHull (K : Set ℂ) : Prop where
  
  subset : K ⊆ upperHalfPlane
  
  bounded : Bornology.IsBounded K
  
  relClosed : ∃ C : Set ℂ, IsClosed C ∧ K = C ∩ upperHalfPlane
  
  complement_open : IsOpen (upperHalfPlane \ K)
  
  complement_connected : IsConnected (upperHalfPlane \ K)


end StatMech.SLE
