/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem isCompact_sixVertexBetheContinuationSet
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N) :
    IsCompact (sixVertexBetheContinuationSet a b N n) := by
  let S : Set (Fin n → Real) := {p | SixVertexClosedRootSimplex p}
  have hbase : IsCompact (Set.Icc a b ×ˢ S) :=
    isCompact_Icc.prod (isCompact_sixVertexClosedRootSimplex n)
  have hU := continuous_sixVertexBetheUpdate_family_clamp
    (n := n) ha hN
  have heqclosed : IsClosed {q : Real × (Fin n → Real) |
      sixVertexBetheUpdate (max a q.1) N n q.2 = q.2} :=
    isClosed_eq hU continuous_snd
  rw [show sixVertexBetheContinuationSet a b N n =
      (Set.Icc a b ×ˢ S) ∩
        {q | sixVertexBetheUpdate (max a q.1) N n q.2 = q.2} by
    ext q
    simp only [sixVertexBetheContinuationSet, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc]
    constructor
    · rintro ⟨hab, hp, hfix⟩
      exact ⟨⟨hab, hp⟩,
        by simpa [max_eq_right hab.1] using hfix⟩
    · rintro ⟨⟨hab, hp⟩, hfix⟩
      exact ⟨hab, hp,
        by simpa [max_eq_right hab.1] using hfix⟩]
  exact hbase.inter_right heqclosed

theorem sixVertexBetheContinuationSet_fiber_nonempty
    {a b t : Real} (ha : 2 < a) (ht : t ∈ Set.Icc a b)
    {N n : Nat} (hN : 0 < N) (hhalf : 2 * n ≤ N) :
    ∃ p, (t, p) ∈ sixVertexBetheContinuationSet a b N n := by
  have htc : 2 < t := ha.trans_le ht.1
  obtain ⟨p, hp, hfix⟩ :=
    exists_sixVertexBetheUpdate_fixedPoint htc hN hhalf
  exact ⟨p, ht, hp, hfix⟩

theorem sixVertexBetheContinuationSet_fst_image
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N) :
    Prod.fst '' sixVertexBetheContinuationSet a b N n = Set.Icc a b := by
  ext t
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.1
  · intro ht
    obtain ⟨p, hp⟩ := sixVertexBetheContinuationSet_fiber_nonempty
      ha ht hN hhalf
    exact ⟨(t, p), hp, rfl⟩


theorem sixVertexBetheContinuationSet_subset_open
    {a b : Real} (ha : 2 < a) {N n : Nat} (hhalf : 2 * n ≤ N) :
    sixVertexBetheContinuationSet a b N n ⊆
      {q | SixVertexOpenRootSimplex q.2} := by
  rintro q ⟨hqIcc, hqclosed, hqfix⟩
  exact sixVertexBetheUpdate_fixedPoint_mem_open
    (ha.trans_le hqIcc.1) hhalf hqclosed hqfix


end
end StatMech.FrontierD
