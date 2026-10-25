/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexNoAdjacentInfinityTopEigenvalue_ge
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N)
    (i : Fin (Fintype.card (SixVertexNoAdjacentSector N n))) :
    (sixVertexNoAdjacentTransferInfinity_isHermitian N n).eigenvalues₀ i ≤
      sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  apply (sixVertexNoAdjacentTransferInfinity_isHermitian N n).eigenvalues₀_antitone
  change (sixVertexNoAdjacentInfinityTopIndex N n hn hhalf).val ≤ i.val
  exact Nat.zero_le _

theorem sixVertexNoAdjacentInfinityTop_hasEigenvalue
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n))
      (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf) := by
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (sixVertexNoAdjacentTransferInfinity_isHermitian N n))
    finrank_euclideanSpace
    (sixVertexNoAdjacentInfinityTopIndex N n hn hhalf)

theorem infinity_matrix_inner_le_abs
    {N n : Nat} (v : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) :
    @inner Real _ _
        (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n) v) v ≤
      @inner Real _ _
        (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n)
          (euclideanAbs v)) (euclideanAbs v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct,
    euclideanAbs, WithLp.ofLp_toLp]
  change (∑ i, v i * ∑ j, sixVertexNoAdjacentTransferInfinity N n i j * v j) ≤
    ∑ i, |v i| * ∑ j,
      sixVertexNoAdjacentTransferInfinity N n i j * |v j|
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    v i * (sixVertexNoAdjacentTransferInfinity N n i j * v j) ≤
        |v i * (sixVertexNoAdjacentTransferInfinity N n i j * v j)| :=
      le_abs_self _
    _ = |v i| * (sixVertexNoAdjacentTransferInfinity N n i j * |v j|) := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (sixVertexNoAdjacentTransferInfinity_nonneg N n i j)]

theorem sixVertexNoAdjacentInfinityTop_exists_nonnegative_eigenvector
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    ∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n),
      v ≠ 0 ∧ (∀ i, 0 ≤ v i) ∧
        sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
          sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
            (fun i => v i) := by
  classical
  let A := sixVertexNoAdjacentTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexNoAdjacentTransferInfinity_isHermitian N n)
  let T' := hT.toSelfAdjoint
  let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
  let e : EuclideanSpace Real (SixVertexNoAdjacentSector N n) :=
    EuclideanSpace.single p 1
  have he : ‖e‖ = 1 := by simp [e]
  have hsphere :
      (Metric.sphere (0 : EuclideanSpace Real
        (SixVertexNoAdjacentSector N n)) 1).Nonempty := ⟨e, by simp [he]⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) 1).exists_isMaxOn
      hsphere T'.val.reApplyInnerSelf_continuous.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  let w := euclideanAbs v
  have hwnorm : ‖w‖ = 1 := by rw [norm_euclideanAbs, hvnorm]
  have hw : w ∈ Metric.sphere
      (0 : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) 1 := by
    simp [hwnorm]
  have hle : T'.val.reApplyInnerSelf v ≤ T'.val.reApplyInnerSelf w := by
    simpa [T', T, A, ContinuousLinearMap.reApplyInnerSelf_apply] using
      infinity_matrix_inner_le_abs v
  have heq : T'.val.reApplyInnerSelf w = T'.val.reApplyInnerSelf v :=
    le_antisymm (hmax hw) hle
  have hwmax : IsMaxOn T'.val.reApplyInnerSelf
      (Metric.sphere 0 1) w := by
    intro z hz
    rw [heq]
    exact hmax hz
  have hwne : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at hwnorm
    norm_num at hwnorm
  let μ : Real := T'.val.rayleighQuotient w
  have heig : Module.End.HasEigenvector T μ w := by
    have hwmax' : IsMaxOn T'.val.reApplyInnerSelf
        (Metric.sphere 0 ‖w‖) w := by simpa only [hwnorm] using hwmax
    exact T'.prop.hasEigenvector_of_isLocalExtrOn hwne (Or.inr hwmax'.localize)
  have hmu : μ = T'.val.reApplyInnerSelf w := by
    simp [μ, ContinuousLinearMap.rayleighQuotient, hwnorm]
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace
    (Module.End.hasEigenvalue_of_hasEigenvector heig)
  have hμtop : μ ≤ sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
    rw [← hi]
    exact sixVertexNoAdjacentInfinityTopEigenvalue_ge N n hn hhalf i
  let i0 := sixVertexNoAdjacentInfinityTopIndex N n hn hhalf
  let u := hT.eigenvectorBasis finrank_euclideanSpace i0
  have hunorm : ‖u‖ = 1 :=
    hT.eigenvectorBasis finrank_euclideanSpace |>.orthonormal.1 i0
  have hu : u ∈ Metric.sphere
      (0 : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) 1 := by
    simp [hunorm]
  have htopμ : sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ≤ μ := by
    have hmaxu := hwmax hu
    have hmaxu' : T'.val.reApplyInnerSelf u ≤
        T'.val.reApplyInnerSelf w := hmaxu
    rw [← hmu] at hmaxu'
    have huEig := hT.apply_eigenvectorBasis finrank_euclideanSpace i0
    have huq : T'.val.reApplyInnerSelf u =
        sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      change @inner Real _ _ (T u) u = _
      rw [huEig, inner_smul_left, real_inner_self_eq_norm_sq, hunorm]
      simp only [one_pow, mul_one]
      change hT.eigenvalues finrank_euclideanSpace i0 =
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr
          (sixVertexNoAdjacentTransferInfinity_isHermitian N n)).eigenvalues
            finrank_euclideanSpace i0
      exact congrArg (fun h : T.IsSymmetric =>
        h.eigenvalues finrank_euclideanSpace i0) (Subsingleton.elim _ _)
    linarith
  have hμeq : μ = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf :=
    le_antisymm hμtop htopμ
  refine ⟨w, hwne, fun i => abs_nonneg _, ?_⟩
  have heqT : T w = μ • w := Module.End.mem_eigenspace_iff.mp heig.1
  have heqFn := congrArg WithLp.ofLp heqT
  simpa [T, A, hμeq, Matrix.ofLp_toLpLin] using heqFn

theorem infinity_matrix_pow_mulVec_of_eigenvector
    {N n : Nat} (v : SixVertexNoAdjacentSector N n → Real) (μ : Real)
    (h : sixVertexNoAdjacentTransferInfinity N n *ᵥ v = μ • v) (k : Nat) :
    (sixVertexNoAdjacentTransferInfinity N n ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

theorem infinity_nonnegative_eigenvector_pos
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N)
    {μ : Real} {v : EuclideanSpace Real (SixVertexNoAdjacentSector N n)}
    (hvne : v ≠ 0) (hvnonneg : ∀ i, 0 ≤ v i)
    (hveig : sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
      μ • (fun i => v i)) :
    ∀ i, 0 < v i := by
  classical
  intro i
  apply lt_of_le_of_ne (hvnonneg i)
  intro hvi
  have hvi0 : v i = 0 := hvi.symm
  obtain ⟨j, hvj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! hall
    apply hvne
    apply WithLp.ofLp_injective 2
    funext j
    simpa using hall j
  have hvjpos : 0 < v j := lt_of_le_of_ne (hvnonneg j) (Ne.symm hvj)
  obtain ⟨k, hk0, hk⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos
      (sixVertexNoAdjacentTransferInfinity_nonneg N n)).mp
      (sixVertexNoAdjacentTransferInfinity_isIrreducible hn hhalf) i j
  have hpoweig := infinity_matrix_pow_mulVec_of_eigenvector
    (fun i => v i) μ hveig k
  have hi := congrFun hpoweig i
  have hsum : 0 < ((sixVertexNoAdjacentTransferInfinity N n ^ k) *ᵥ
      (fun i => v i)) i := by
    rw [Matrix.mulVec]
    apply Finset.sum_pos'
    · intro z _
      exact mul_nonneg
        (Matrix.pow_apply_nonneg
          (sixVertexNoAdjacentTransferInfinity_nonneg N n) k i z)
        (hvnonneg z)
    · exact ⟨j, Finset.mem_univ j, mul_pos hk hvjpos⟩
  simp only [Pi.smul_apply, smul_eq_mul, hvi0, mul_zero] at hi
  linarith

theorem sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    ∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n),
      (∀ i, 0 < v i) ∧
        sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
          sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
            (fun i => v i) := by
  obtain ⟨v, hvne, hvnonneg, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_nonnegative_eigenvector hn hhalf
  exact ⟨v, infinity_nonnegative_eigenvector_pos hn hhalf hvne hvnonneg hveig,
    hveig⟩

theorem sixVertexNoAdjacentInfinityTopEigenvalue_pos
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    0 < sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  classical
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let even := sixVertexNoAdjacentAlternatingEven N n hn hhalf
  let odd := sixVertexNoAdjacentAlternatingOdd N n hn hhalf
  have heo : (sixVertexNoAdjacentInfinityGraph N n).Adj even odd :=
    sixVertexNoAdjacentInfinityGraph_adj_alternating hn hhalf
  have hentry : sixVertexNoAdjacentTransferInfinity N n even odd = 1 := by
    rw [← sixVertexNoAdjacentInfinityGraph_adjMatrix]
    simp [SimpleGraph.adjMatrix, heo]
  have heven := congrFun hveig even
  have hsum : v odd ≤
      (sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i)) even := by
    rw [Matrix.mulVec, dotProduct]
    calc
      v odd = sixVertexNoAdjacentTransferInfinity N n even odd * v odd := by
        rw [hentry, one_mul]
      _ ≤ ∑ i, sixVertexNoAdjacentTransferInfinity N n even i * v i := by
        apply Finset.single_le_sum
          (s := (Finset.univ : Finset (SixVertexNoAdjacentSector N n)))
          (f := fun i => sixVertexNoAdjacentTransferInfinity N n even i * v i)
        · intro j _
          exact mul_nonneg (sixVertexNoAdjacentTransferInfinity_nonneg N n even j)
            (hvpos j).le
        · exact Finset.mem_univ odd
  simp only [Pi.smul_apply, smul_eq_mul] at heven
  rw [heven] at hsum
  nlinarith [hvpos even, hvpos odd]

theorem sixVertexNoAdjacentInfinityTop_eigenspace_finrank
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.finrank Real (Module.End.eigenspace
      (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n))
      (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  classical
  letI : Nonempty (SixVertexNoAdjacentSector N n) :=
    ⟨sixVertexNoAdjacentAlternatingEven N n hn hhalf⟩
  let A := sixVertexNoAdjacentTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  let μ := sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  have hvne : v ≠ 0 := by
    intro hv0
    have := hvpos (sixVertexNoAdjacentAlternatingEven N n hn hhalf)
    simp [hv0] at this
  have hvT : T v = μ • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, A, μ, Matrix.ofLp_toLpLin] using hveig
  have hvMem : v ∈ Module.End.eigenspace T μ :=
    Module.End.mem_eigenspace_iff.mpr hvT
  let vv : Module.End.eigenspace T μ := ⟨v, hvMem⟩
  have hvvne : vv ≠ 0 := by
    intro h
    apply hvne
    exact Subtype.ext_iff.mp h
  apply finrank_eq_one vv hvvne
  intro zz
  let z : EuclideanSpace Real (SixVertexNoAdjacentSector N n) := zz.1
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp zz.2
  let ratio : SixVertexNoAdjacentSector N n → Real := fun i => z i / v i
  have himage : (Finset.univ.image ratio).Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  let r : Real := (Finset.univ.image ratio).min' himage
  have hr (i : SixVertexNoAdjacentSector N n) : r ≤ ratio i :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  obtain ⟨i0, _, hi0⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image ratio) himage)
  let w : EuclideanSpace Real (SixVertexNoAdjacentSector N n) := z - r • v
  have hwnonneg : ∀ i, 0 ≤ w i := by
    intro i
    change 0 ≤ z i - r * v i
    exact sub_nonneg.mpr ((le_div_iff₀ (hvpos i)).mp (hr i))
  have hwi0 : w i0 = 0 := by
    change z i0 - r * v i0 = 0
    have hir : ratio i0 = r := hi0
    dsimp [ratio] at hir
    rw [← hir]
    field_simp [(hvpos i0).ne']
    ring
  have hwT : T w = μ • w := by
    simp only [w, map_sub, map_smul, hzT, hvT]
    module
  have hweig : A *ᵥ (fun i => w i) = μ • (fun i => w i) := by
    have hwT' := congrArg WithLp.ofLp hwT
    simpa [T, A, Matrix.ofLp_toLpLin] using hwT'
  have hwzero : w = 0 := by
    by_contra hwne
    have hpos := infinity_nonnegative_eigenvector_pos hn hhalf hwne hwnonneg hweig i0
    rw [hwi0] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change r • v = z
  exact (sub_eq_zero.mp hwzero).symm


theorem sixVertexNoAdjacentInfinityTop_isSimplePerron
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    0 < sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ∧
      (∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n),
        (∀ i, 0 < v i) ∧
          sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
            sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
              (fun i => v i)) ∧
      Module.finrank Real (Module.End.eigenspace
        (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n))
        (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  exact ⟨sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf,
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf,
    sixVertexNoAdjacentInfinityTop_eigenspace_finrank hn hhalf⟩


end
end StatMech.FrontierD
