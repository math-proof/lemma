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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part8
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem euclideanAbs_apply {α : Type*} [Fintype α]
    (v : EuclideanSpace ℝ α) (i : α) : euclideanAbs v i = |v i| :=
  rfl

theorem norm_euclideanAbs {α : Type*} [Fintype α] (v : EuclideanSpace ℝ α) :
    ‖euclideanAbs v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem matrix_inner_le_abs {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (v : EuclideanSpace ℝ α) :
    @inner ℝ _ _ (Matrix.toEuclideanLin A v) v ≤
      @inner ℝ _ _ (Matrix.toEuclideanLin A (euclideanAbs v)) (euclideanAbs v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct,
    euclideanAbs, WithLp.ofLp_toLp]
  change (∑ i, v i * ∑ j, A i j * v j) ≤
    ∑ i, |v i| * ∑ j, A i j * |v j|
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  calc
    v i * (A i j * v j) ≤ |v i * (A i j * v j)| := le_abs_self _
    _ = |v i| * (A i j * |v j|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hA i j)]

theorem sixVertexSectorTop_exists_nonnegative_eigenvector {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) :
    ∃ v : EuclideanSpace ℝ (SixVertexSector N n),
      v ≠ 0 ∧ (∀ i, 0 ≤ v i) ∧
        sixVertexSectorTransfer N n c *ᵥ (fun i => v i) =
          sixVertexSectorTopEigenvalue N n hn c • (fun i => v i) := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let A := sixVertexSectorTransfer N n c
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexSectorTransfer_isHermitian N n c)
  let T' := hT.toSelfAdjoint
  let p := sixVertexPackedSector N n hn
  let e : EuclideanSpace ℝ (SixVertexSector N n) := EuclideanSpace.single p 1
  have he : ‖e‖ = 1 := by simp [e]
  have hsphere : (Metric.sphere (0 : EuclideanSpace ℝ (SixVertexSector N n)) 1).Nonempty :=
    ⟨e, by simp [he]⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace ℝ (SixVertexSector N n)) 1).exists_isMaxOn hsphere
      T'.val.reApplyInnerSelf_continuous.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  let w := euclideanAbs v
  have hwnorm : ‖w‖ = 1 := by rw [norm_euclideanAbs, hvnorm]
  have hw : w ∈ Metric.sphere (0 : EuclideanSpace ℝ (SixVertexSector N n)) 1 := by
    simp [hwnorm]
  have hle : T'.val.reApplyInnerSelf v ≤ T'.val.reApplyInnerSelf w := by
    simpa [T', T, A, w, ContinuousLinearMap.reApplyInnerSelf_apply,
      LinearMap.IsSymmetric.toSelfAdjoint_apply] using
      matrix_inner_le_abs A (sixVertexSectorTransfer_nonneg (LT.lt.le hc)) v
  have heq : T'.val.reApplyInnerSelf w = T'.val.reApplyInnerSelf v :=
    le_antisymm (hmax hw) hle
  have hwmax : IsMaxOn T'.val.reApplyInnerSelf (Metric.sphere 0 1) w := by
    intro z hz
    rw [heq]
    exact hmax hz
  have hwne : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at hwnorm
    norm_num at hwnorm
  let μ : ℝ := T'.val.rayleighQuotient w
  have heig : Module.End.HasEigenvector T μ w := by
    have hwmax' : IsMaxOn T'.val.reApplyInnerSelf (Metric.sphere 0 ‖w‖) w := by
      simpa only [hwnorm] using hwmax
    exact T'.prop.hasEigenvector_of_isLocalExtrOn hwne (Or.inr hwmax'.localize)
  have hmu : μ = T'.val.reApplyInnerSelf w := by
    simp [μ, ContinuousLinearMap.rayleighQuotient, hwnorm]
  have hmuEig : Module.End.HasEigenvalue T μ :=
    Module.End.hasEigenvalue_of_hasEigenvector heig
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace hmuEig
  have hμtop : μ ≤ sixVertexSectorTopEigenvalue N n hn c := by
    rw [← hi]
    exact sixVertexSectorTopEigenvalue_ge N n hn c i
  let i0 := sixVertexSectorTopIndex N n hn
  let u := hT.eigenvectorBasis finrank_euclideanSpace i0
  have hunorm : ‖u‖ = 1 := hT.eigenvectorBasis finrank_euclideanSpace |>.orthonormal.1 i0
  have hu : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (SixVertexSector N n)) 1 := by
    simp [hunorm]
  have htopμ : sixVertexSectorTopEigenvalue N n hn c ≤ μ := by
    have hmaxu := hwmax hu
    have hmaxu' : T'.val.reApplyInnerSelf u ≤ T'.val.reApplyInnerSelf w := hmaxu
    rw [← hmu] at hmaxu'
    have huEig := hT.apply_eigenvectorBasis finrank_euclideanSpace i0
    have huq : T'.val.reApplyInnerSelf u = sixVertexSectorTopEigenvalue N n hn c := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      change @inner ℝ _ _ (T u) u = _
      rw [huEig]
      rw [inner_smul_left, real_inner_self_eq_norm_sq, hunorm]
      simp only [one_pow, mul_one]
      change hT.eigenvalues finrank_euclideanSpace i0 =
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr
          (sixVertexSectorTransfer_isHermitian N n c)).eigenvalues
            finrank_euclideanSpace i0
      exact congrArg (fun h : T.IsSymmetric => h.eigenvalues finrank_euclideanSpace i0)
        (Subsingleton.elim _ _)
    linarith
  have hμeq : μ = sixVertexSectorTopEigenvalue N n hn c := le_antisymm hμtop htopμ
  refine ⟨w, hwne, fun i => abs_nonneg _, ?_⟩
  have heqT : T w = μ • w := Module.End.mem_eigenspace_iff.mp heig.1
  have heqFn := congrArg WithLp.ofLp heqT
  simpa [T, A, hμeq, Matrix.ofLp_toLpLin] using heqFn

theorem matrix_pow_mulVec_of_eigenvector {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (v : α → ℝ) (μ : ℝ)
    (h : A *ᵥ v = μ • v) (k : ℕ) :
    (A ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

theorem sixVertexSectorTop_exists_positive_eigenvector {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) :
    ∃ v : EuclideanSpace ℝ (SixVertexSector N n),
      (∀ i, 0 < v i) ∧
        sixVertexSectorTransfer N n c *ᵥ (fun i => v i) =
          sixVertexSectorTopEigenvalue N n hn c • (fun i => v i) := by
  classical
  obtain ⟨v, hvne, hvnonneg, hveig⟩ :=
    sixVertexSectorTop_exists_nonnegative_eigenvector hn hc
  refine ⟨v, ?_, hveig⟩
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
  let K := sixVertexPrimitiveExponent N n hn hc
  have hpoweig := matrix_pow_mulVec_of_eigenvector
    (sixVertexSectorTransfer N n c) (fun i => v i)
    (sixVertexSectorTopEigenvalue N n hn c) hveig K
  have hi := congrFun hpoweig i
  have hsum : 0 < ((sixVertexSectorTransfer N n c) ^ K *ᵥ (fun i => v i)) i := by
    rw [Matrix.mulVec]
    apply Finset.sum_pos'
    · intro z hz
      exact mul_nonneg (sixVertexSectorTransfer_pow_nonneg hc.le i z) (hvnonneg z)
    · exact ⟨j, Finset.mem_univ j,
        mul_pos (sixVertexSectorTransfer_primitivePower_pos hn hc i j) hvjpos⟩
  simp only [Pi.smul_apply, smul_eq_mul, hvi0, mul_zero] at hi
  linarith

theorem sixVertexSectorTopEigenvalue_pos {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) : 0 < sixVertexSectorTopEigenvalue N n hn c := by
  classical
  obtain ⟨v, hvpos, hveig⟩ := sixVertexSectorTop_exists_positive_eigenvector hn hc
  let i : SixVertexSector N n := sixVertexPackedSector N n hn
  have hi := congrFun hveig i
  have hsum : 2 * v i ≤ (sixVertexSectorTransfer N n c *ᵥ (fun j => v j)) i := by
    rw [Matrix.mulVec, dotProduct]
    have hterm : sixVertexSectorTransfer N n c i i * v i = 2 * v i := by
      simp [sixVertexSectorTransfer, sixVertexTransfer]
    rw [← hterm]
    change sixVertexSectorTransfer N n c i i * v i ≤
      ∑ j ∈ (Finset.univ : Finset (SixVertexSector N n)),
        sixVertexSectorTransfer N n c i j * v j
    apply Finset.single_le_sum (f := fun j : SixVertexSector N n =>
      sixVertexSectorTransfer N n c i j * v j)
    · intro j hj
      exact mul_nonneg (sixVertexSectorTransfer_nonneg hc.le i j) (hvpos j).le
    · exact Finset.mem_univ i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  rw [hi] at hsum
  nlinarith [hvpos i]

theorem sixVertexSector_nonnegative_eigenvector_pos {N n : ℕ} (hn : n ≤ N)
    {c μ : ℝ} (hc : 0 < c) {v : EuclideanSpace ℝ (SixVertexSector N n)}
    (hvne : v ≠ 0) (hvnonneg : ∀ i, 0 ≤ v i)
    (hveig : sixVertexSectorTransfer N n c *ᵥ (fun i => v i) = μ • (fun i => v i)) :
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
  let K := sixVertexPrimitiveExponent N n hn hc
  have hpoweig := matrix_pow_mulVec_of_eigenvector
    (sixVertexSectorTransfer N n c) (fun i => v i) μ hveig K
  have hi := congrFun hpoweig i
  have hsum : 0 < ((sixVertexSectorTransfer N n c) ^ K *ᵥ (fun i => v i)) i := by
    rw [Matrix.mulVec]
    apply Finset.sum_pos'
    · intro z hz
      exact mul_nonneg (sixVertexSectorTransfer_pow_nonneg hc.le i z) (hvnonneg z)
    · exact ⟨j, Finset.mem_univ j,
        mul_pos (sixVertexSectorTransfer_primitivePower_pos hn hc i j) hvjpos⟩
  simp only [Pi.smul_apply, smul_eq_mul, hvi0, mul_zero] at hi
  linarith

theorem sixVertexSectorTop_eigenspace_finrank {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) :
    Module.finrank ℝ (Module.End.eigenspace
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c))
      (sixVertexSectorTopEigenvalue N n hn c)) = 1 := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let A := sixVertexSectorTransfer N n c
  let T := Matrix.toEuclideanLin A
  let μ := sixVertexSectorTopEigenvalue N n hn c
  obtain ⟨v, hvpos, hveig⟩ := sixVertexSectorTop_exists_positive_eigenvector hn hc
  have hvne : v ≠ 0 := by
    intro hv0
    let i : SixVertexSector N n := sixVertexPackedSector N n hn
    have := hvpos i
    simp [hv0] at this
  have hvT : T v = μ • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, A, μ, Matrix.ofLp_toLpLin] using hveig
  have hvMem : v ∈ Module.End.eigenspace T μ := Module.End.mem_eigenspace_iff.mpr hvT
  let vv : Module.End.eigenspace T μ := ⟨v, hvMem⟩
  have hvvne : vv ≠ 0 := by
    intro h
    apply hvne
    exact Subtype.ext_iff.mp h
  apply finrank_eq_one vv hvvne
  intro zz
  let z : EuclideanSpace ℝ (SixVertexSector N n) := zz.1
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp zz.2
  let ratio : SixVertexSector N n → ℝ := fun i => z i / v i
  have himage : (Finset.univ.image ratio).Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let r : ℝ := (Finset.univ.image ratio).min' himage
  have hr (i : SixVertexSector N n) : r ≤ ratio i := by
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  obtain ⟨i0, hi0mem, hi0⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image ratio) himage)
  let w : EuclideanSpace ℝ (SixVertexSector N n) := z - r • v
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
    have := sixVertexSector_nonnegative_eigenvector_pos hn hc hwne hwnonneg hweig i0
    rw [hwi0] at this
    exact lt_irrefl 0 this
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change r • v = z
  have := sub_eq_zero.mp hwzero
  exact this.symm

theorem sixVertexSector_eigenvalue_abs_le_top {N n : ℕ} (hn : n ≤ N)
    {c μ : ℝ} (hc : 0 < c) {z : EuclideanSpace ℝ (SixVertexSector N n)}
    (hzne : z ≠ 0)
    (hzeig : sixVertexSectorTransfer N n c *ᵥ (fun i => z i) = μ • (fun i => z i)) :
    |μ| ≤ sixVertexSectorTopEigenvalue N n hn c := by
  classical
  let A := sixVertexSectorTransfer N n c
  let top := sixVertexSectorTopEigenvalue N n hn c
  obtain ⟨v, hvpos, hveig⟩ := sixVertexSectorTop_exists_positive_eigenvector hn hc
  let S : ℝ := ∑ i, v i * |z i|
  have hSpos : 0 < S := by
    obtain ⟨j, hzj⟩ : ∃ j, z j ≠ 0 := by
      by_contra! hall
      apply hzne
      apply WithLp.ofLp_injective 2
      funext j
      simpa using hall j
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hvpos i).le (abs_nonneg _)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hvpos j) (abs_pos.mpr hzj)⟩
  have hcoord (i : SixVertexSector N n) :
      |μ| * |z i| ≤ ∑ j, A i j * |z j| := by
    have hi := congrFun hzeig i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    rw [← abs_mul, ← hi]
    calc
      |∑ j, A i j * z j| ≤ ∑ j, |A i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, A i j * |z j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg (sixVertexSectorTransfer_nonneg hc.le i j)]
  have hweighted :
      ∑ i, v i * (|μ| * |z i|) ≤
        ∑ i, v i * ∑ j, A i j * |z j| := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hcoord i) (hvpos i).le
  have hleft : ∑ i, v i * (|μ| * |z i|) = |μ| * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright : ∑ i, v i * ∑ j, A i j * |z j| = top * S := by
    calc
      ∑ i, v i * ∑ j, A i j * |z j| =
          ∑ i, ∑ j, v i * (A i j * |z j|) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, v i * (A i j * |z j|) := Finset.sum_comm
      _ = ∑ j, |z j| * ∑ i, A j i * v i := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            have hsym : A i j = A j i := by
              simpa [A, sixVertexSectorTransfer] using
                (sixVertexTransfer_symmetric N c
                  (sixVertexSectorRow i) (sixVertexSectorRow j))
            rw [hsym]
            ring
      _ = ∑ j, |z j| * (top * v j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' := congrFun hveig j
            simpa [A, top, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
              congrArg (fun x : ℝ => |z j| * x) hj'
      _ = top * S := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [hleft, hright] at hweighted
  nlinarith

theorem positiveMatrix_eigenvectors_collinear
    {α : Type*} [Fintype α] [Nonempty α]
    (B : Matrix α α ℝ) (hBpos : ∀ i j, 0 < B i j)
    {ρ : ℝ} {v z : EuclideanSpace ℝ α}
    (hvpos : ∀ i, 0 < v i)
    (hveig : B *ᵥ (fun i => v i) = ρ • (fun i => v i))
    (hzeig : B *ᵥ (fun i => z i) = ρ • (fun i => z i)) :
    ∃ r : ℝ, r • v = z := by
  classical
  let ratio : α → ℝ := fun i => z i / v i
  have himage : (Finset.univ.image ratio).Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  let r : ℝ := (Finset.univ.image ratio).min' himage
  have hr (i : α) : r ≤ ratio i :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  obtain ⟨i0, hi0mem, hi0⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image ratio) himage)
  let w : EuclideanSpace ℝ α := z - r • v
  have hwnonneg : ∀ i, 0 ≤ w i := by
    intro i
    change 0 ≤ z i - r * v i
    exact sub_nonneg.mpr ((le_div_iff₀ (hvpos i)).mp (hr i))
  have hwi0 : w i0 = 0 := by
    change z i0 - r * v i0 = 0
    have hir : ratio i0 = r := hi0
    dsimp [ratio] at hir
    rw [← hir]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ (hvpos i0).ne').symm
  have hweig : B *ᵥ (fun i => w i) = ρ • (fun i => w i) := by
    change B *ᵥ ((fun i => z i) - r • (fun i => v i)) =
      ρ • ((fun i => z i) - r • (fun i => v i))
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hzeig, hveig]
    module
  have hwzero : w = 0 := by
    by_contra hwne
    obtain ⟨j, hwj⟩ : ∃ j, w j ≠ 0 := by
      by_contra! hall
      apply hwne
      apply WithLp.ofLp_injective 2
      funext j
      simpa using hall j
    have hwjpos : 0 < w j := lt_of_le_of_ne (hwnonneg j) (Ne.symm hwj)
    have hsum : 0 < (B *ᵥ (fun i => w i)) i0 := by
      rw [Matrix.mulVec]
      apply Finset.sum_pos'
      · intro i hi
        exact mul_nonneg (hBpos i0 i).le (hwnonneg i)
      · exact ⟨j, Finset.mem_univ j, mul_pos (hBpos i0 j) hwjpos⟩
    have hi := congrFun hweig i0
    simp only [Pi.smul_apply, smul_eq_mul, hwi0, mul_zero] at hi
    linarith
  refine ⟨r, ?_⟩
  change r • v = z
  exact (sub_eq_zero.mp hwzero).symm


theorem sixVertexSector_eigenvalue_abs_lt_top {N n : ℕ} (hn : n ≤ N)
    {c μ : ℝ} (hc : 0 < c)
    (hμ : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ)
    (hne : μ ≠ sixVertexSectorTopEigenvalue N n hn c) :
    |μ| < sixVertexSectorTopEigenvalue N n hn c := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let A := sixVertexSectorTransfer N n c
  let T := Matrix.toEuclideanLin A
  let top := sixVertexSectorTopEigenvalue N n hn c
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have hzne : z ≠ 0 := hz.2
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp hz.1
  have hzeig : A *ᵥ (fun i => z i) = μ • (fun i => z i) := by
    have hzT' := congrArg WithLp.ofLp hzT
    simpa [T, A, Matrix.ofLp_toLpLin] using hzT'
  have habsle : |μ| ≤ top := by
    exact sixVertexSector_eigenvalue_abs_le_top hn hc hzne hzeig
  apply lt_of_le_of_ne habsle
  intro habseq
  have htoppos : 0 < top := sixVertexSectorTopEigenvalue_pos hn hc
  have hμneg : μ = -top := by
    rcases le_total 0 μ with hμnonneg | hμnonpos
    · rw [abs_of_nonneg hμnonneg] at habseq
      exact False.elim (hne habseq)
    · rw [abs_of_nonpos hμnonpos] at habseq
      linarith
  obtain ⟨v, hvpos, hveig⟩ := sixVertexSectorTop_exists_positive_eigenvector hn hc
  let K := sixVertexPrimitiveExponent N n hn hc
  let L := 2 * K
  let B := A ^ L
  have hLeven : Even L := by
    exact even_two_mul K
  have hBpos (i j : SixVertexSector N n) : 0 < B i j := by
    change 0 < (A ^ (2 * K)) i j
    rw [two_mul]
    apply sixVertexSectorTransfer_mul_pos (z := sixVertexPackedSector N n hn) hc.le
    · exact sixVertexSectorTransfer_primitivePower_pos hn hc i _
    · exact sixVertexSectorTransfer_primitivePower_pos hn hc _ j
  have hvpow : B *ᵥ (fun i => v i) = top ^ L • (fun i => v i) := by
    exact matrix_pow_mulVec_of_eigenvector A (fun i => v i) top hveig L
  have hzpow : B *ᵥ (fun i => z i) = top ^ L • (fun i => z i) := by
    have h := matrix_pow_mulVec_of_eigenvector A (fun i => z i) μ hzeig L
    rw [hμneg, hLeven.neg_pow] at h
    exact h
  obtain ⟨r, hr⟩ := positiveMatrix_eigenvectors_collinear B hBpos hvpos hvpow hzpow
  have hrne : r ≠ 0 := by
    intro hr0
    apply hzne
    rw [← hr, hr0, zero_smul]
  have hvT : T v = top • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, A, Matrix.ofLp_toLpLin] using hveig
  rw [← hr] at hzT
  simp only [map_smul, hvT, smul_smul] at hzT
  let i : SixVertexSector N n := sixVertexPackedSector N n hn
  have hi := congrArg (fun q : EuclideanSpace ℝ (SixVertexSector N n) => q i) hzT
  change (r * top) * v i = (μ * r) * v i at hi
  exfalso
  apply hne
  change μ = top
  have hi' : top * (r * v i) = μ * (r * v i) := by
    calc
      top * (r * v i) = r * top * v i := by ring
      _ = μ * r * v i := hi
      _ = μ * (r * v i) := by ring
  exact (mul_right_cancel₀ (mul_ne_zero hrne (hvpos i).ne') hi').symm


theorem sixVertexSector_eigenvalue_abs_le_top_of_nonzero
    {N n : ℕ} (hn : n ≤ N) {c μ : ℝ} (hc : 0 < c)
    {z : EuclideanSpace ℝ (SixVertexSector N n)} (hzne : z ≠ 0)
    (hzeig : sixVertexSectorTransfer N n c *ᵥ (fun i => z i) =
      μ • (fun i => z i)) :
    |μ| ≤ sixVertexSectorTopEigenvalue N n hn c :=
  sixVertexSector_eigenvalue_abs_le_top hn hc hzne hzeig


theorem sixVertexSectorTop_isPerronFrobenius {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) :
    0 < sixVertexSectorTopEigenvalue N n hn c ∧
      (∃ v : EuclideanSpace ℝ (SixVertexSector N n),
        (∀ i, 0 < v i) ∧
          sixVertexSectorTransfer N n c *ᵥ (fun i => v i) =
            sixVertexSectorTopEigenvalue N n hn c • (fun i => v i)) ∧
      Module.finrank ℝ (Module.End.eigenspace
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c))
        (sixVertexSectorTopEigenvalue N n hn c)) = 1 ∧
      ∀ μ : ℝ,
        Module.End.HasEigenvalue
            (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ →
          μ ≠ sixVertexSectorTopEigenvalue N n hn c →
            |μ| < sixVertexSectorTopEigenvalue N n hn c := by
  exact ⟨sixVertexSectorTopEigenvalue_pos hn hc,
    sixVertexSectorTop_exists_positive_eigenvector hn hc,
    sixVertexSectorTop_eigenspace_finrank hn hc,
    fun μ hμ hne => sixVertexSector_eigenvalue_abs_lt_top hn hc hμ hne⟩


theorem sixVertexLambda_isPerronFrobenius (N r : ℕ) (hN : Even N)
    (hr : r ≤ N / 2) {c : ℝ} (hc : 0 < c) :
    0 < sixVertexLambda N r hN hr c ∧
      (∃ v : EuclideanSpace ℝ (SixVertexSector N (N / 2 - r)),
        (∀ i, 0 < v i) ∧
          sixVertexSectorTransfer N (N / 2 - r) c *ᵥ (fun i => v i) =
            sixVertexLambda N r hN hr c • (fun i => v i)) ∧
      Module.finrank ℝ (Module.End.eigenspace
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N (N / 2 - r) c))
        (sixVertexLambda N r hN hr c)) = 1 ∧
      ∀ μ : ℝ,
        Module.End.HasEigenvalue
            (Matrix.toEuclideanLin (sixVertexSectorTransfer N (N / 2 - r) c)) μ →
          μ ≠ sixVertexLambda N r hN hr c →
            |μ| < sixVertexLambda N r hN hr c := by
  let hn : N / 2 - r ≤ N := (Nat.sub_le _ _).trans (Nat.div_le_self N 2)
  simpa only [sixVertexLambda] using
    (sixVertexSectorTop_isPerronFrobenius hn hc)

end StatMech.FrontierD
