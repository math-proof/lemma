/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary.Part3


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


namespace HexDomain

variable {V : Type*} [DecidableEq V] (D : HexDomain V)


noncomputable def boundarySum (P : D.InteriorPairing) : ℂ :=
  ∑ e ∈ D.incidences \ P.interior, D.incTerm e


end HexDomain
end StatMech.Universality
