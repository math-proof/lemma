/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Theorem.StatisticalMechanics.Code.SLE.Cardy
public section

open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

structure Mobius (K : Type*) [Field K] where
  
  a : K
  
  b : K
  
  c : K
  
  d : K
  
  det_ne_zero : a * d - b * c ≠ 0


end StatMech.SLE
