/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part9


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


open HexWalk


noncomputable def hexZSummand (a : ℂ) (h0 : ℤ) (x : ℝ) (ts : List ℤ) : ℝ≥0∞ :=
  haveI := Classical.propDecidable ((ofTurns a h0 ts).IsLegalSAW)
  if (ofTurns a h0 ts).IsLegalSAW then ENNReal.ofReal (x ^ (ofTurns a h0 ts).numVertices) else 0


noncomputable def hexZ (a : ℂ) (h0 : ℤ) (x : ℝ) : ℝ≥0∞ :=
  ∑' ts : List ℤ, hexZSummand a h0 x ts


end StatMech.Universality
