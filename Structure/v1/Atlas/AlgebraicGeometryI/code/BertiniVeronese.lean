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
import Def.v1.Atlas.AlgebraicGeometryI.code.BertiniVeronese.Part2


noncomputable section

open MvPolynomial Finset

namespace BertiniVeronese

/-- A smooth projective subvariety of `ℙⁿ`: a finite collection of homogeneous defining
polynomials such that at every nonzero point of the variety, the Jacobian condition holds. -/
structure SmoothProjectiveVariety (k : Type) [Field k] (n : ℕ) where
  definingPolys : Finset (MvPolynomial (Fin (n + 1)) k)
  polysHomogeneous : ∀ p ∈ definingPolys, ∃ d, p.IsHomogeneous d
  onVariety (x : Fin (n + 1) → k) : Prop :=
    ∀ p ∈ definingPolys, MvPolynomial.eval x p = 0
  isSmooth : ∀ x : Fin (n + 1) → k, x ≠ 0 → onVariety x →
    ∀ v : Fin (n + 1) → k, v ≠ 0 →
      (∀ p ∈ definingPolys, ∀ i : Fin (n + 1),
        MvPolynomial.eval x (MvPolynomial.pderiv i p) = 0) →
      False

end BertiniVeronese
end
