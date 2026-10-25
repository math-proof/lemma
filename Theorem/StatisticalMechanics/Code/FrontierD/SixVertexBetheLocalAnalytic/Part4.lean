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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem isCompact_sixVertexBetheFixedPointSet
    {c : Real} (hc : 2 < c) (N n : Nat) :
    IsCompact (sixVertexBetheFixedPointSet c N n) := by
  have hclosed : IsClosed {p : Fin n → Real |
      sixVertexBetheUpdate c N n p = p} :=
    isClosed_eq (continuous_sixVertexBetheUpdate hc N n) continuous_id
  exact (isCompact_sixVertexClosedRootSimplex n).inter_right hclosed

theorem sixVertexBetheFixedPointSet_nonempty
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N) :
    (sixVertexBetheFixedPointSet c N n).Nonempty := by
  obtain ⟨p, hp, hfix⟩ :=
    exists_sixVertexBetheUpdate_fixedPoint hc hN hhalf
  exact ⟨p, hp, hfix⟩


theorem sixVertexBetheFixedPointSet_subset_open
    {c : Real} (hc : 2 < c) {N n : Nat} (hhalf : 2 * n ≤ N) :
    sixVertexBetheFixedPointSet c N n ⊆
      {p | SixVertexOpenRootSimplex p} := by
  rintro p ⟨hp, hfix⟩
  exact sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hp hfix

theorem sixVertexBetheFixedPointSet_eq_solutionSet
    {c : Real} {N n : Nat} (hN : 0 < N) :
    sixVertexBetheFixedPointSet c N n =
      {p | SixVertexClosedRootSimplex p ∧
        SixVertexSatisfiesBetheEquations c N n p} := by
  ext p
  simp only [sixVertexBetheFixedPointSet, Set.mem_setOf_eq]
  rw [sixVertexBetheUpdate_eq_self_iff hN p]

theorem continuous_sixVertexBetheResidual_family_clamp
    {a : Real} (ha : 2 < a) (N n : Nat) :
    Continuous (fun q : Real × (Fin n → Real) =>
      fun j => sixVertexBetheResidual (max a q.1) N n q.2 j) := by
  rw [continuous_iff_continuousAt]
  intro q
  have hc : 2 < max a q.1 := ha.trans_le (le_max_left _ _)
  have hbase := (analyticAt_sixVertexBetheResidual_family N n
    (max a q.1, q.2) hc).continuousAt
  have hmap : ContinuousAt
      (fun z : Real × (Fin n → Real) => (max a z.1, z.2)) q := by
    fun_prop
  exact hbase.comp
    (f := fun z : Real × (Fin n → Real) => (max a z.1, z.2))
    (x := q) hmap

theorem continuous_sixVertexBetheUpdate_family_clamp
    {a : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N) :
    Continuous (fun q : Real × (Fin n → Real) =>
      sixVertexBetheUpdate (max a q.1) N n q.2) := by
  have hres := continuous_sixVertexBetheResidual_family_clamp ha N n
  have heq : (fun q : Real × (Fin n → Real) =>
      sixVertexBetheUpdate (max a q.1) N n q.2) =
      fun q => q.2 - (1 / (N : Real)) •
        (fun j => sixVertexBetheResidual (max a q.1) N n q.2 j) := by
    funext q j
    have h := sixVertexBetheResidual_eq_updateSub hN q.2 j
      (c := max a q.1)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change _ = q.2 j - (1 / (N : Real)) * _
    change sixVertexBetheResidual (max a q.1) N n q.2 j = _ at h
    have hNr : (0 : Real) < N := by exact_mod_cast hN
    rw [h]
    field_simp [hNr.ne']
    ring
  rw [heq]
  exact continuous_snd.sub (continuous_const.smul hres)


end
end StatMech.FrontierD
