/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BertiniVeronese


noncomputable section

open MvPolynomial Finset

namespace BertiniVeronese

/-- The space of homogeneous polynomials of degree `d` in `n + 1` variables over `k`. -/
abbrev HomogeneousPolys (k : Type) [Field k] (n d : ℕ) : Type :=
  { f : MvPolynomial (Fin (n + 1)) k // f.IsHomogeneous d }

end BertiniVeronese
end
