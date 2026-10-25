/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorInfinityTopEigenvalue_ge
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N)
    (i : Fin (Fintype.card (SixVertexSector N n))) :
    (sixVertexSectorTransferInfinity_isHermitian N n).eigenvalues₀ i ≤
      sixVertexSectorInfinityTopEigenvalue N n hn hhalf := by
  apply (sixVertexSectorTransferInfinity_isHermitian N n).eigenvalues₀_antitone
  change (sixVertexSectorInfinityTopIndex N n hn hhalf).val ≤ i.val
  exact Nat.zero_le _

theorem sixVertexSectorInfinityTop_hasEigenvalue
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n))
      (sixVertexSectorInfinityTopEigenvalue N n hn hhalf) := by
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (sixVertexSectorTransferInfinity_isHermitian N n))
    finrank_euclideanSpace
    (sixVertexSectorInfinityTopIndex N n hn hhalf)


theorem sixVertexSectorInfinityTop_le_of_positive_supersolution
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N)
    {R : Real} (q : SixVertexSector N n → Real)
    (hqpos : ∀ i, 0 < q i)
    (hq : ∀ i, (sixVertexSectorTransferInfinity N n *ᵥ q) i ≤
      R * q i) :
    sixVertexSectorInfinityTopEigenvalue N n hn hhalf ≤ R := by
  classical
  let A := sixVertexSectorTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  let μ := sixVertexSectorInfinityTopEigenvalue N n hn hhalf
  obtain ⟨z, hzmem, hzne⟩ :=
    (sixVertexSectorInfinityTop_hasEigenvalue N n hn hhalf).exists_hasEigenvector
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp hzmem
  have hzeig : A *ᵥ (fun i ↦ z i) = μ • (fun i ↦ z i) := by
    have hz := congrArg WithLp.ofLp hzT
    simpa [T, A, Matrix.ofLp_toLpLin] using hz
  let S : Real := ∑ i, q i * |z i|
  have hS : 0 < S := by
    obtain ⟨j, hzj⟩ : ∃ j, z j ≠ 0 := by
      by_contra! hall
      apply hzne
      apply WithLp.ofLp_injective 2
      funext j
      simpa using hall j
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hqpos i).le (abs_nonneg _)
    · exact ⟨j, Finset.mem_univ j,
        mul_pos (hqpos j) (abs_pos.mpr hzj)⟩
  have hcoord (i : SixVertexSector N n) :
      |μ| * |z i| ≤ ∑ j, A i j * |z j| := by
    have hi := congrFun hzeig i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    rw [← abs_mul, ← hi]
    calc
      |∑ j, A i j * z j| ≤ ∑ j, |A i j * z j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, A i j * |z j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg]
        exact sixVertexSectorTransferInfinity_nonneg N n i j
  have hweighted :
      ∑ i, q i * (|μ| * |z i|) ≤
        ∑ i, q i * ∑ j, A i j * |z j| := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hcoord i) (hqpos i).le
  have hleft : ∑ i, q i * (|μ| * |z i|) = |μ| * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htranspose :
      (∑ i, q i * ∑ j, A i j * |z j|) =
        ∑ j, |z j| * (A *ᵥ q) j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [show A i j = A j i by
      exact sixVertexSectorTransferInfinity_symmetric N n i j]
    ring
  have hright : (∑ j, |z j| * (A *ᵥ q) j) ≤ R * S := by
    calc
      (∑ j, |z j| * (A *ᵥ q) j) ≤
          ∑ j, |z j| * (R * q j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hq j) (abs_nonneg _)
      _ = R * S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hleft, htranspose] at hweighted
  have habs : |μ| * S ≤ R * S := hweighted.trans hright
  have hmule : μ ≤ |μ| := le_abs_self μ
  nlinarith


theorem sixVertexSectorInfinityTopEigenvalue_eq_noAdjacent
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    sixVertexSectorInfinityTopEigenvalue N n hn hhalf =
      sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  classical
  let ρ := sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf
  have hρpos : 0 < ρ := sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let q : SixVertexSector N n → Real := fun x ↦
    if hx : SixVertexSectorNoAdjacent x then v ⟨x, hx⟩ else 1
  have hqpos : ∀ x, 0 < q x := by
    intro x
    by_cases hx : SixVertexSectorNoAdjacent x
    · simp [q, hx, hvpos ⟨x, hx⟩]
    · simp [q, hx]
  have hmul : sixVertexSectorTransferInfinity N n *ᵥ q =
      sixVertexSectorTransferInfinity N n *ᵥ
        sixVertexNoAdjacentZeroExtend (fun i ↦ v i) := by
    funext x
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : SixVertexSectorNoAdjacent y
    · simp [q, hy, sixVertexNoAdjacentZeroExtend]
    · rw [sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right x hy]
      simp
  have hq : ∀ x, (sixVertexSectorTransferInfinity N n *ᵥ q) x ≤ ρ * q x := by
    intro x
    rw [hmul, sixVertexSectorTransferInfinity_mulVec_zeroExtend, hveig]
    by_cases hx : SixVertexSectorNoAdjacent x
    · simp [q, hx, sixVertexNoAdjacentZeroExtend, ρ]
    · simp [q, hx, sixVertexNoAdjacentZeroExtend, hρpos.le]
  have hfullLe : sixVertexSectorInfinityTopEigenvalue N n hn hhalf ≤ ρ :=
    sixVertexSectorInfinityTop_le_of_positive_supersolution hn hhalf q hqpos hq
  have hactiveEig : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n)) ρ := by
    obtain ⟨w, hwne, hweigFull⟩ :=
      sixVertexSectorTransferInfinity_exists_Perron_eigenvector hn hhalf
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hwne⟩
    apply Module.End.mem_eigenspace_iff.mpr
    apply WithLp.ofLp_injective 2
    simpa [ρ, Matrix.ofLp_toLpLin] using hweigFull
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexSectorTransferInfinity_isHermitian N n)
  obtain ⟨i, hi⟩ := hsym.exists_eigenvalues_eq finrank_euclideanSpace hactiveEig
  have hactiveLe : ρ ≤ sixVertexSectorInfinityTopEigenvalue N n hn hhalf := by
    rw [← hi]
    exact sixVertexSectorInfinityTopEigenvalue_ge N n hn hhalf i
  exact le_antisymm hfullLe hactiveLe


theorem sixVertexSectorInfinityTop_isSimplePerron
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    0 < sixVertexSectorInfinityTopEigenvalue N n hn hhalf ∧
      Module.finrank Real (Module.End.eigenspace
        (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n))
        (sixVertexSectorInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  rw [sixVertexSectorInfinityTopEigenvalue_eq_noAdjacent hn hhalf]
  exact ⟨sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf,
    sixVertexSectorTransferInfinity_Perron_eigenspace_finrank hn hhalf⟩

end
end StatMech.FrontierD
