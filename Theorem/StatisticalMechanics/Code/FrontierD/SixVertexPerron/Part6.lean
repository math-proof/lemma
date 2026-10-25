/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part5
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexLower_eq_self_iff {N n : ℕ} (x : SixVertexSector N n)
    (hn : n ≤ N) : sixVertexLowerSector x = x ↔ x = sixVertexPackedSector N n hn := by
  constructor
  · intro hx
    apply (Set.powersetCard.ofFinEmbEquiv (n := n) (I := Fin N)).symm.injective
    change sixVertexSectorPosition x =
      sixVertexSectorPosition (sixVertexPackedSector N n hn)
    rw [sixVertexSectorPosition_packed]
    ext i
    have hpos : i.val ≤ (sixVertexSectorPosition x i).val :=
      fin_val_le_of_strictMono _ (sixVertexSectorPosition x).strictMono i
    have hi := congrArg (fun f : Fin n ↪o Fin N => (f i).val)
      (sixVertexSectorPosition_lower x)
    rw [hx] at hi
    simp only [lowerSectorEmbedding, OrderEmbedding.coe_ofStrictMono] at hi
    simp only [OrderEmbedding.coe_ofStrictMono, Fin.val_castLE]
    omega
  · rintro rfl
    apply (Set.powersetCard.ofFinEmbEquiv (n := n) (I := Fin N)).symm.injective
    change sixVertexSectorPosition (sixVertexLowerSector (sixVertexPackedSector N n hn)) =
      sixVertexSectorPosition (sixVertexPackedSector N n hn)
    rw [sixVertexSectorPosition_lower, sixVertexSectorPosition_packed]
    ext i
    simp [lowerSectorEmbedding]

theorem sixVertexSectorHeight_lower_lt {N n : ℕ} (x : SixVertexSector N n)
    (hne : sixVertexLowerSector x ≠ x) :
    sixVertexSectorHeight (sixVertexLowerSector x) < sixVertexSectorHeight x := by
  rw [sixVertexSectorHeight, sixVertexSectorHeight]
  apply Finset.sum_lt_sum
  · intro i hi
    have h := (sixVertexLower_positionsForwardInterlaced x).1 i
    exact_mod_cast h
  · by_contra! hnot
    apply hne
    apply (Set.powersetCard.ofFinEmbEquiv (n := n) (I := Fin N)).symm.injective
    change sixVertexSectorPosition (sixVertexLowerSector x) = sixVertexSectorPosition x
    ext i
    have hle := (sixVertexLower_positionsForwardInterlaced x).1 i
    exact Nat.le_antisymm hle (hnot i (Finset.mem_univ i))


theorem sixVertexSectorTransfer_nonneg {N n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (x y : SixVertexSector N n) : 0 ≤ sixVertexSectorTransfer N n c x y :=
  sixVertexTransfer_nonneg hc _ _

theorem sixVertexSectorTransfer_pow_nonneg {N n k : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (x y : SixVertexSector N n) : 0 ≤ (sixVertexSectorTransfer N n c ^ k) x y :=
  Matrix.pow_apply_nonneg (sixVertexSectorTransfer_nonneg hc) k x y

theorem sixVertexSectorTransfer_pow_symmetric {N n k : ℕ} (c : ℝ)
    (x y : SixVertexSector N n) :
    (sixVertexSectorTransfer N n c ^ k) x y =
      (sixVertexSectorTransfer N n c ^ k) y x := by
  have h := (sixVertexSectorTransfer_isHermitian N n c).pow k
  rw [Matrix.IsHermitian.ext_iff] at h
  simpa only [star_id_of_comm] using (h x y).symm

theorem sixVertexSectorTransfer_self_pos {N n : ℕ} (c : ℝ)
    (x : SixVertexSector N n) : 0 < sixVertexSectorTransfer N n c x x := by
  simp [sixVertexSectorTransfer, sixVertexTransfer]

theorem sixVertexSectorTransfer_mul_pos {N n k l : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {x y z : SixVertexSector N n}
    (hxz : 0 < (sixVertexSectorTransfer N n c ^ k) x z)
    (hzy : 0 < (sixVertexSectorTransfer N n c ^ l) z y) :
    0 < (sixVertexSectorTransfer N n c ^ (k + l)) x y := by
  rw [pow_add, Matrix.mul_apply]
  apply Finset.sum_pos'
  · intro w hw
    exact mul_nonneg (sixVertexSectorTransfer_pow_nonneg hc x w)
      (sixVertexSectorTransfer_pow_nonneg hc w y)
  · exact ⟨z, Finset.mem_univ z, mul_pos hxz hzy⟩

theorem sixVertexSectorTransfer_exists_pow_pos_to_packed {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) (x : SixVertexSector N n) :
    ∃ k > 0, 0 < (sixVertexSectorTransfer N n c ^ k) x
      (sixVertexPackedSector N n hn) := by
  classical
  induction hheight : sixVertexSectorHeight x using Nat.strong_induction_on generalizing x with
  | h m ih =>
      by_cases hxp : x = sixVertexPackedSector N n hn
      · subst x
        refine ⟨1, Nat.zero_lt_one, ?_⟩
        simpa using sixVertexSectorTransfer_self_pos c (sixVertexPackedSector N n hn)
      · have hlower : sixVertexLowerSector x ≠ x := by
          intro hfix
          exact hxp ((sixVertexLower_eq_self_iff x hn).mp hfix)
        have hlt : sixVertexSectorHeight (sixVertexLowerSector x) < m := by
          rw [← hheight]
          exact sixVertexSectorHeight_lower_lt x hlower
        obtain ⟨k, hk0, hk⟩ :=
          ih (sixVertexSectorHeight (sixVertexLowerSector x)) hlt
            (sixVertexLowerSector x) rfl
        refine ⟨1 + k, by omega, ?_⟩
        apply sixVertexSectorTransfer_mul_pos (z := sixVertexLowerSector x) hc.le
        · rw [sixVertexSectorTransfer_pow_symmetric c x (sixVertexLowerSector x)]
          simpa using sixVertexSectorTransfer_lower_pos hc x
        · exact hk

theorem sixVertexSectorTransfer_isIrreducible {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) :
    (sixVertexSectorTransfer N n c).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos (sixVertexSectorTransfer_nonneg hc.le)]
  intro x y
  obtain ⟨k, hk0, hk⟩ := sixVertexSectorTransfer_exists_pow_pos_to_packed hn hc x
  obtain ⟨l, hl0, hl⟩ := sixVertexSectorTransfer_exists_pow_pos_to_packed hn hc y
  refine ⟨k + l, Nat.add_pos_left hk0 l, ?_⟩
  apply sixVertexSectorTransfer_mul_pos hc.le hk
  rwa [sixVertexSectorTransfer_pow_symmetric]

theorem sixVertexSectorTransfer_pow_self_pos {N n m : ℕ} {c : ℝ} (hc : 0 < c)
    (x : SixVertexSector N n) :
    0 < (sixVertexSectorTransfer N n c ^ m) x x := by
  induction m with
  | zero => simp
  | succ m ih =>
      apply sixVertexSectorTransfer_mul_pos (z := x) hc.le ih
      simpa using sixVertexSectorTransfer_self_pos c x

end StatMech.FrontierD
