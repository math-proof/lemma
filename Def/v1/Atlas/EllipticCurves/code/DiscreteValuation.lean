/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DiscreteValuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.EllipticCurves.code.DiscreteValuation
attribute [instance] DiscreteValuation.discrete


namespace DiscreteValuation

variable {F : Type*} [Field F] (v : DiscreteValuation F)

/-- The valuation subring $R = \{x \in F : v(x) \geq 0\}$ of a discrete valuation. -/
def valuationSubring : ValuationSubring F :=
  v.val.valuationSubring

/-- The underlying subring of $F$ associated to a discrete valuation. -/
def valuationRing : Subring F :=
  v.valuationSubring.toSubring

/-- The unique maximal ideal $\mathfrak{m} = \{x \in R : v(x) \geq 1\}$ of the valuation ring. -/
noncomputable def maximalIdeal : Ideal v.valuationSubring :=
  IsLocalRing.maximalIdeal v.valuationSubring

/-- An element $u \in F$ is a uniformizer for $v$ when $v(u) = 1$. -/
def IsUniformizerOf (u : F) : Prop :=
  v.val.IsUniformizer u

end DiscreteValuation
