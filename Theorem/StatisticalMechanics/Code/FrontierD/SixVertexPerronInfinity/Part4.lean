/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexNoAdjacentZeroExtend_apply
    {N n : Nat} (q : SixVertexNoAdjacentSector N n → Real)
    (x : SixVertexNoAdjacentSector N n) :
    sixVertexNoAdjacentZeroExtend q x.1 = q x := by
  simp [sixVertexNoAdjacentZeroExtend, x.2]

theorem sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply
    {N n : Nat} (q : SixVertexNoAdjacentSector N n → Real)
    (x : SixVertexSector N n) (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexSectorTransferInfinity N n *ᵥ
        sixVertexNoAdjacentZeroExtend q) x =
      (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) ⟨x, hx⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  change (∑ y : SixVertexSector N n,
    sixVertexSectorTransferInfinity N n x y *
      sixVertexNoAdjacentZeroExtend q y) =
    ∑ y : SixVertexNoAdjacentSector N n,
      sixVertexSectorTransferInfinity N n x y.1 * q y
  calc
    (∑ y : SixVertexSector N n,
      sixVertexSectorTransferInfinity N n x y *
        sixVertexNoAdjacentZeroExtend q y) =
        ∑ y ∈ (Finset.univ.filter fun y : SixVertexSector N n ↦
          SixVertexSectorNoAdjacent y),
          sixVertexSectorTransferInfinity N n x y *
            sixVertexNoAdjacentZeroExtend q y := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : SixVertexSectorNoAdjacent y <;>
        simp [sixVertexNoAdjacentZeroExtend, hy]
    _ = ∑ y : SixVertexNoAdjacentSector N n,
        sixVertexSectorTransferInfinity N n x y.1 *
          sixVertexNoAdjacentZeroExtend q y.1 :=
      Finset.sum_subtype _ (by simp) _
    _ = ∑ y : SixVertexNoAdjacentSector N n,
        sixVertexSectorTransferInfinity N n x y.1 * q y := by
      apply Finset.sum_congr rfl
      intro y _
      simp

theorem sixVertexSectorTransferInfinity_mulVec_zeroExtend
    {N n : Nat} (q : SixVertexNoAdjacentSector N n → Real) :
    sixVertexSectorTransferInfinity N n *ᵥ sixVertexNoAdjacentZeroExtend q =
      sixVertexNoAdjacentZeroExtend
        (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) := by
  funext x
  by_cases hx : SixVertexSectorNoAdjacent x
  · rw [sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply q x hx]
    simp [sixVertexNoAdjacentZeroExtend, hx]
  · simp only [Matrix.mulVec, dotProduct]
    rw [show (∑ y, sixVertexSectorTransferInfinity N n x y *
        sixVertexNoAdjacentZeroExtend q y) = 0 by
      apply Finset.sum_eq_zero
      intro y _
      rw [sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hx]
      simp]
    simp [sixVertexNoAdjacentZeroExtend, hx]


theorem sixVertexSectorTransferInfinity_exists_Perron_eigenvector
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    ∃ v : EuclideanSpace Real (SixVertexSector N n),
      v ≠ 0 ∧
      (sixVertexSectorTransferInfinity N n *ᵥ (fun i ↦ v i) =
        sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
          (fun i ↦ v i)) := by
  obtain ⟨w, hwpos, hweig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let v : EuclideanSpace Real (SixVertexSector N n) :=
    WithLp.toLp 2 (sixVertexNoAdjacentZeroExtend (fun i ↦ w i))
  have hvne : v ≠ 0 := by
    intro hv
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    have hp := congrArg (fun z : EuclideanSpace Real (SixVertexSector N n) ↦
      z p.1) hv
    simp [v, p] at hp
    exact (hwpos p).ne' hp
  refine ⟨v, hvne, ?_⟩
  rw [show (fun i ↦ v i) =
      sixVertexNoAdjacentZeroExtend (fun i ↦ w i) by rfl,
    sixVertexSectorTransferInfinity_mulVec_zeroExtend, hweig]
  funext x
  by_cases hx : SixVertexSectorNoAdjacent x
  · simp [sixVertexNoAdjacentZeroExtend, hx]
  · simp [sixVertexNoAdjacentZeroExtend, hx]


theorem sixVertexSectorTransferInfinity_Perron_eigenspace_finrank
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.finrank Real (Module.End.eigenspace
      (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n))
      (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  classical
  let A := sixVertexSectorTransferInfinity N n
  let B := sixVertexNoAdjacentTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  let U := Matrix.toEuclideanLin B
  let μ := sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf
  have hμpos : 0 < μ := sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let V : EuclideanSpace Real (SixVertexSector N n) :=
    WithLp.toLp 2 (sixVertexNoAdjacentZeroExtend (fun i ↦ v i))
  have hVT : T V = μ • V := by
    apply WithLp.ofLp_injective 2
    simp only [T, A, V, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
      WithLp.ofLp_smul]
    rw [sixVertexSectorTransferInfinity_mulVec_zeroExtend, hveig]
    funext x
    by_cases hx : SixVertexSectorNoAdjacent x <;>
      simp [μ, sixVertexNoAdjacentZeroExtend, hx]
  have hVMem : V ∈ Module.End.eigenspace T μ :=
    Module.End.mem_eigenspace_iff.mpr hVT
  let VV : Module.End.eigenspace T μ := ⟨V, hVMem⟩
  have hVVne : VV ≠ 0 := by
    intro hzero
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    have hp := congrArg (fun z : EuclideanSpace Real (SixVertexSector N n) ↦
      z p.1) (Subtype.ext_iff.mp hzero)
    simp [VV, V, p] at hp
    exact (hvpos p).ne' hp
  apply finrank_eq_one VV hVVne
  intro zz
  let z : EuclideanSpace Real (SixVertexSector N n) := zz.1
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp zz.2
  have hzeig : A *ᵥ (fun i ↦ z i) = μ • (fun i ↦ z i) := by
    have hz := congrArg WithLp.ofLp hzT
    simpa [T, A, Matrix.ofLp_toLpLin] using hz
  have hzinactive (x : SixVertexSector N n)
      (hx : ¬ SixVertexSectorNoAdjacent x) : z x = 0 := by
    have hxcoord := congrFun hzeig x
    have hxleft : (A *ᵥ (fun i ↦ z i)) x = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro y _
      simp [A, sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hx]
    rw [hxleft] at hxcoord
    simp only [Pi.smul_apply, smul_eq_mul] at hxcoord
    nlinarith
  let w : EuclideanSpace Real (SixVertexNoAdjacentSector N n) :=
    WithLp.toLp 2 (fun i ↦ z i.1)
  have hzext : sixVertexNoAdjacentZeroExtend (fun i ↦ w i) =
      (fun x ↦ z x) := by
    funext x
    by_cases hx : SixVertexSectorNoAdjacent x
    · simp [sixVertexNoAdjacentZeroExtend, hx, w]
    · simp [sixVertexNoAdjacentZeroExtend, hx, hzinactive x hx]
  have hweig : B *ᵥ (fun i ↦ w i) = μ • (fun i ↦ w i) := by
    funext x
    have hxcoord := congrFun hzeig x.1
    rw [← hzext,
      sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply
        (fun i ↦ w i) x.1 x.2] at hxcoord
    simpa [A, B, μ, sixVertexNoAdjacentZeroExtend, x.2] using hxcoord
  have hwT : U w = μ • w := by
    apply WithLp.ofLp_injective 2
    simpa [U, B, Matrix.ofLp_toLpLin] using hweig
  have hwMem : w ∈ Module.End.eigenspace U μ :=
    Module.End.mem_eigenspace_iff.mpr hwT
  have hvT : U v = μ • v := by
    apply WithLp.ofLp_injective 2
    simpa [U, B, μ, Matrix.ofLp_toLpLin] using hveig
  have hvMem : v ∈ Module.End.eigenspace U μ :=
    Module.End.mem_eigenspace_iff.mpr hvT
  let vv : Module.End.eigenspace U μ := ⟨v, hvMem⟩
  have hvvne : vv ≠ 0 := by
    intro hzero
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    have hp := congrArg (fun q : EuclideanSpace Real
      (SixVertexNoAdjacentSector N n) ↦ q p) (Subtype.ext_iff.mp hzero)
    simp [vv] at hp
    exact (hvpos p).ne' hp
  have hactiveRank : Module.finrank Real (Module.End.eigenspace U μ) = 1 := by
    simpa [U, B, μ] using
      sixVertexNoAdjacentInfinityTop_eigenspace_finrank hn hhalf
  have hspan : Real ∙ vv = ⊤ :=
    (finrank_eq_one_iff_of_nonzero vv hvvne).mp hactiveRank
  have hwmemspan : (⟨w, hwMem⟩ : Module.End.eigenspace U μ) ∈
      Real ∙ vv := by
    rw [hspan]
    trivial
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hwmemspan
  refine ⟨r, Subtype.ext ?_⟩
  change r • V = z
  apply WithLp.ofLp_injective 2
  funext x
  by_cases hx : SixVertexSectorNoAdjacent x
  · have hr' := congrArg (fun q : EuclideanSpace Real
        (SixVertexNoAdjacentSector N n) ↦ q ⟨x, hx⟩)
      (congrArg Subtype.val hr)
    simpa [VV, V, vv, w, sixVertexNoAdjacentZeroExtend, hx] using hr'
  · simp [V, sixVertexNoAdjacentZeroExtend, hx, hzinactive x hx]

theorem sixVertexSectorTransferInfinity_isHermitian (N n : Nat) :
    (sixVertexSectorTransferInfinity N n).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro x y
  simp only [star_id_of_comm]
  exact sixVertexSectorTransferInfinity_symmetric N n y x

end
end StatMech.FrontierD
