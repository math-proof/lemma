/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.RealAnalysis.code.Integration.Basic.Part2
public import Theorem.Real.Atlas.v1.RealAnalysis.code.Integration.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Def.v1.Atlas.RealAnalysis.code.Integration.ModulusContinuity
public section

open Set Filter Topology Finset


namespace Integration

/-- `T'` is a tagged refinement of `T` when every subinterval of `T'` is contained
in some subinterval of `T` (witnessed by `assign`), and the subintervals of `T'`
assigned to each `T`-subinterval telescope to its length. This captures the
condition `x ⊂ x'` in Theorem II. -/
structure TaggedPartition.IsTaggedRefinement (T T' : TaggedPartition a b) where
  assign : Fin T'.n → Fin T.n
  contained_left : ∀ j : Fin T'.n, T.points (assign j).castSucc ≤ T'.points j.castSucc
  contained_right : ∀ j : Fin T'.n, T'.points j.succ ≤ T.points (assign j).succ
  telescope : ∀ k : Fin T.n,
    ∑ j ∈ Finset.univ.filter (fun j => assign j = k),
      (T'.points j.succ - T'.points j.castSucc) = T.points k.succ - T.points k.castSucc

end Integration
