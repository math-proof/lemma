/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part5
open Finset


namespace StatMech.FrontierD

@[simp] theorem sixVertexRectangleStraightExtend_horizontal_castSucc
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows N M) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleStraightExtend (q := q) z ω).horizontal
        ((Fin.castAdd r i).castSucc, Fin.castAdd q j) =
      ω.horizontal (i.castSucc, j) := by
  have hx : (Fin.castAdd r i).castSucc = Fin.castAdd (r + 1) i := by
    ext
    rfl
  rw [hx]
  simp [sixVertexRectangleStraightExtend]

@[simp] theorem sixVertexRectangleStraightExtend_horizontal_succ
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) M)
    (i : Fin (N + 1)) (j : Fin M) :
    (sixVertexRectangleStraightExtend (q := q) z ω).horizontal
        ((Fin.castAdd r i).succ, Fin.castAdd q j) =
      ω.horizontal (i.succ, j) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hx : (Fin.castAdd r (Fin.last N)).succ =
        Fin.natAdd (N + 1) (0 : Fin (r + 1)) := by
      ext
      simp
    rw [hx]
    simp [sixVertexRectangleStraightExtend]
  · have hx : (Fin.castAdd r i.castSucc).succ =
        Fin.castAdd (r + 1) i.succ := by
      ext
      rfl
    rw [hx]
    simp [sixVertexRectangleStraightExtend]

@[simp] theorem sixVertexRectangleStraightExtend_vertical_castSucc
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows N M) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleStraightExtend (q := q) z ω).vertical
        (Fin.castAdd r i, (Fin.castAdd q j).castSucc) =
      ω.vertical (i, j.castSucc) := by
  have hy : (Fin.castAdd q j).castSucc = Fin.castAdd (q + 1) j := by
    ext
    rfl
  rw [hy]
  simp [sixVertexRectangleStraightExtend]

@[simp] theorem sixVertexRectangleStraightExtend_vertical_succ
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows N (M + 1))
    (i : Fin N) (j : Fin (M + 1)) :
    (sixVertexRectangleStraightExtend (q := q) z ω).vertical
        (Fin.castAdd r i, (Fin.castAdd q j).succ) =
      ω.vertical (i, j.succ) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hy : (Fin.castAdd q (Fin.last M)).succ =
        Fin.natAdd (M + 1) (0 : Fin (q + 1)) := by
      ext
      simp
    rw [hy]
    simp [sixVertexRectangleStraightExtend]
  · have hy : (Fin.castAdd q j.castSucc).succ =
        Fin.castAdd (q + 1) j.succ := by
      ext
      rfl
    rw [hy]
    simp [sixVertexRectangleStraightExtend]


theorem sixVertexRectangleStraightExtend_localWeight_base
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1))
    (i : Fin (N + 1)) (j : Fin (M + 1)) :
    (sixVertexRectangleStraightExtend z ω).localWeight c
        (Fin.castAdd r i, Fin.castAdd q j) = ω.localWeight c (i, j) := by
  simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount,
      SixVertexRectangleArrows.IsCType]


theorem sixVertexRectangleStraightExtend_localWeight_right
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1))
    (i : Fin r) (j : Fin (M + 1)) :
    (sixVertexRectangleStraightExtend z ω).localWeight c
        (Fin.natAdd (N + 1) i, Fin.castAdd q j) = 1 := by
  have hx₀ : (Fin.natAdd (N + 1) i).castSucc =
      Fin.natAdd (N + 1) i.castSucc := by
    ext
    rfl
  have hx₁ : (Fin.natAdd (N + 1) i).succ =
      Fin.natAdd (N + 1) i.succ := by
    ext
    rfl
  cases hz : z i <;> cases hh : ω.horizontal (Fin.last (N + 1), j) <;>
    simp [sixVertexRectangleStraightExtend, hx₀, hx₁,
      SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount,
      SixVertexRectangleArrows.IsCType, hz, hh]


theorem sixVertexRectangleStraightExtend_localWeight_top
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1))
    (i : Fin ((N + 1) + r)) (j : Fin q) :
    (sixVertexRectangleStraightExtend z ω).localWeight c
        (i, Fin.natAdd (M + 1) j) = 1 := by
  have hy₀ : (Fin.natAdd (M + 1) j).castSucc =
      Fin.natAdd (M + 1) j.castSucc := by
    ext
    rfl
  have hy₁ : (Fin.natAdd (M + 1) j).succ =
      Fin.natAdd (M + 1) j.succ := by
    ext
    rfl
  refine Fin.addCases (m := N + 1) (n := r) ?_ ?_ i
  · intro x
    cases hv : ω.vertical (x, Fin.last (M + 1)) <;>
      simp [sixVertexRectangleStraightExtend, hy₀, hy₁,
        SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount,
        SixVertexRectangleArrows.IsCType, hv]
  · intro x
    cases hz : z x <;>
      simp [sixVertexRectangleStraightExtend, hy₀, hy₁,
        SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount,
        SixVertexRectangleArrows.IsCType, hz]


theorem sixVertexRectangleStraightExtend_weight
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1)) :
    (sixVertexRectangleStraightExtend (q := q) z ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexRectangleArrows.weight,
    Fintype.prod_prod_type]
  rw [Fin.prod_univ_add]
  have hbase :
      (∏ i : Fin (N + 1),
        ∏ j : Fin ((M + 1) + q),
          (sixVertexRectangleStraightExtend z ω).localWeight c
            (Fin.castAdd r i, j)) =
        ∏ i : Fin (N + 1), ∏ j : Fin (M + 1), ω.localWeight c (i, j) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Fin.prod_univ_add]
    simp [sixVertexRectangleStraightExtend_localWeight_base,
      sixVertexRectangleStraightExtend_localWeight_top]
  rw [hbase]
  have hright :
      (∏ i : Fin r,
        ∏ j : Fin ((M + 1) + q),
          (sixVertexRectangleStraightExtend z ω).localWeight c
            (Fin.natAdd (N + 1) i, j)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Fin.prod_univ_add]
    simp [sixVertexRectangleStraightExtend_localWeight_right,
      sixVertexRectangleStraightExtend_localWeight_top]
  rw [hright, mul_one]
  exact (Fintype.prod_prod_type fun ij : Fin (N + 1) × Fin (M + 1) =>
    ω.localWeight c ij).symm


end StatMech.FrontierD
