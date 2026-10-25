/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Structure.v1.Atlas.RealAnalysis.code.Integration.Basic


namespace Integration

variable {a b : ℝ}

/-- The mesh (or norm) `‖x‖` of a partition: the maximum length
`max_k (x_k - x_{k-1})` of its subintervals. Defined to be `0` for the trivial
partition with `n = 0`. -/
noncomputable def Partition.mesh (P : Partition a b) : ℝ :=
  if h : P.n = 0 then 0
  else
    Finset.sup' (Finset.univ (α := Fin P.n))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
      (fun i => P.points i.succ - P.points i.castSucc)

/-- The underlying set `{x_0, x_1, …, x_n}` of points of a partition. -/
def Partition.pointSet (P : Partition a b) : Set ℝ :=
  Set.range P.points

/-- `Q` is a refinement of `P` if every point of `P` appears in `Q`, i.e. the
underlying point set of `P` is contained in that of `Q`. -/
def Partition.IsRefinement (Q P : Partition a b) : Prop :=
  P.pointSet ⊆ Q.pointSet

/-- The Riemann sum `S_f(x, ξ) = ∑_k f(ξ_k) (x_k - x_{k-1})` of a function `f`
with respect to a tagged partition `T`. -/
noncomputable def riemannSum (f : ℝ → ℝ) (T : TaggedPartition a b) : ℝ :=
  ∑ i : Fin T.n, f (T.tags i) * (T.points i.succ - T.points i.castSucc)

end Integration
