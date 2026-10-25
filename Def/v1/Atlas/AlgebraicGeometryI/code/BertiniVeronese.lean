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


noncomputable section

open MvPolynomial Finset

namespace BertiniVeronese

/-- The number of monomials of degree `d` in `n+1` variables: `C(n+d, d)`. This is the dimension
of the space of degree-`d` forms used in the Veronese embedding. -/
def veroneseMonomialCount (n d : ℕ) : ℕ := Nat.choose (n + d) d

/-- Dimension of the target projective space of the degree-`d` Veronese embedding of `ℙⁿ`. -/
def veroneseEmbedDim (n d : ℕ) : ℕ := Nat.choose (n + d) d - 1

/-- Dimension of the parameter space of degree-`d` hypersurfaces in `ℙⁿ`. -/
def hypersurfaceParamDim (n d : ℕ) : ℕ := Nat.choose (n + d) d - 1

/-- Number of conditions imposed by requiring smoothness at a fixed point: the value of `f` and
the `n` partial derivatives, so `n + 1` conditions. -/
def smoothnessConditionCount (n : ℕ) : ℕ := n + 1

end BertiniVeronese
end
