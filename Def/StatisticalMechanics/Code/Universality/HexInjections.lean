/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexSAWwt (a : ℂ) (h0 : ℤ) (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable ((HexWalk.ofTurns a h0 ts).IsLegalSAW)
  if (HexWalk.ofTurns a h0 ts).IsLegalSAW then x ^ (HexWalk.ofTurns a h0 ts).numVertices else 0


end StatMech.Universality
