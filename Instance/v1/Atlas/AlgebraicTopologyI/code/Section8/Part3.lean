/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.Section8.Part4


namespace AlgebraicTopologyI

open AlgebraicTopologyI

attribute [instance] NatChainComplex.instAddCommGroup

/-- The homology group of a naturally indexed chain complex inherits its abelian
group structure from the quotient construction. -/
noncomputable instance NatChainComplex.instAddCommGroupHomology
    (C : NatChainComplex) (n : ℕ) : AddCommGroup (C.homologyGroup n) :=
  QuotientAddGroup.Quotient.addCommGroup _

end AlgebraicTopologyI
