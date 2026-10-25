/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Def.v1.Atlas.AlgebraicTopologyI.code.Section17


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- $\mathbf{RP}^n$ carries the quotient topology inherited from $S^n$. -/
instance (n : ℕ) : TopologicalSpace (RPn n) :=
  instTopologicalSpaceQuotient (s := antipodalSetoid n)

end RealProjectiveSpace
end
