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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section17


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- **Proposition 17.1**. The integral singular homology of real projective $n$-space:
$H_0(\mathbf{RP}^n) = \mathbb{Z}$,
$H_n(\mathbf{RP}^n) = \mathbb{Z}$ if $n$ is odd,
$H_k(\mathbf{RP}^n) = \mathbb{Z}/2$ for odd $k$ with $0 < k < n$,
and zero otherwise. -/
def homologyGroup (n k : ℕ) : AddCommGrpCat :=
  if k = 0 then AddCommGrpCat.of ℤ
  else if k = n ∧ Odd n then AddCommGrpCat.of ℤ
  else if Odd k ∧ k < n then AddCommGrpCat.of (ZMod 2)
  else AddCommGrpCat.of PUnit

/-- The image subgroup of the cellular differential
$\partial_{k+1} : C_{k+1}(\mathbf{RP}^n) \to C_k(\mathbf{RP}^n) \cong \mathbb{Z}$:
all of $\mathbb{Z}$ when $k > n$, zero when $k = n$ or $k$ is even with $k < n$, and $2\mathbb{Z}$
when $k$ is odd with $k < n$. -/
def rpnImageSubgroup (n k : ℕ) : AddSubgroup ℤ :=
  if k > n then ⊤
  else if k = n then ⊥
  else if Odd k then AddSubgroup.zmultiples (2 : ℤ)
  else ⊥

/-- The cellular chain homology of $\mathbf{RP}^n$ in degree $k$, computed as
$\mathbb{Z} / \text{(image of }\partial_{k+1}\text{)}$. -/
def rpnChainHomology (n k : ℕ) : AddCommGrpCat :=
  if k > n then AddCommGrpCat.of PUnit
  else if k = 0 then AddCommGrpCat.of (ℤ ⧸ rpnImageSubgroup n 0)
  else if Odd k then AddCommGrpCat.of (ℤ ⧸ rpnImageSubgroup n k)
  else AddCommGrpCat.of PUnit

end RealProjectiveSpace
end
