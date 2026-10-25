/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.SLE.Defs.Part6
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

structure LoewnerChain where
  
  driving : ℝ → ℝ
  
  driving_continuous : Continuous driving
  
  maps : ℝ → ℂ → ℂ
  

  loewner : SatisfiesLoewnerEquation driving maps


end StatMech.SLE
