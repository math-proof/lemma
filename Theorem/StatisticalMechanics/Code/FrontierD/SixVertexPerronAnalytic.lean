/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem analyticAt_sixVertexSectorTransfer_apply
    (N n : Nat) (x y : SixVertexSector N n) (c : Real) :
    AnalyticAt Real (fun t ↦ sixVertexSectorTransfer N n t x y) c := by
  unfold sixVertexSectorTransfer sixVertexTransfer
  split_ifs <;> fun_prop


theorem analyticAt_sixVertexSectorCharacteristicDet
    (N n : Nat) (z : Real × Real) :
    AnalyticAt Real (fun q : Real × Real ↦ Matrix.det
      (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n q.1)) z := by
  rw [show (fun q : Real × Real ↦ Matrix.det
        (q.2 • (1 : Matrix (SixVertexSector N n)
            (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n q.1)) =
      fun q ↦ ∑ sigma : Equiv.Perm (SixVertexSector N n),
        Equiv.Perm.sign sigma * ∏ i,
          (q.2 • (1 : Matrix (SixVertexSector N n)
              (SixVertexSector N n) Real) -
            sixVertexSectorTransfer N n q.1) (sigma i) i by
    funext q
    rw [Matrix.det_apply']]
  rw [show (fun q : Real × Real ↦
      ∑ sigma : Equiv.Perm (SixVertexSector N n),
        (((Equiv.Perm.sign sigma : Int) : Real)) * ∏ i,
          (q.2 • (1 : Matrix (SixVertexSector N n)
              (SixVertexSector N n) Real) -
            sixVertexSectorTransfer N n q.1) (sigma i) i) =
      ∑ sigma : Equiv.Perm (SixVertexSector N n), fun q : Real × Real ↦
        (((Equiv.Perm.sign sigma : Int) : Real)) * ∏ i,
          (q.2 • (1 : Matrix (SixVertexSector N n)
              (SixVertexSector N n) Real) -
            sixVertexSectorTransfer N n q.1) (sigma i) i by
    funext q
    simp]
  apply Finset.analyticAt_sum
  intro sigma _
  apply AnalyticAt.mul
  · fun_prop
  · rw [show (fun q : Real × Real ↦ ∏ i : SixVertexSector N n,
        (q.2 • (1 : Matrix (SixVertexSector N n)
            (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n q.1) (sigma i) i) =
      ∏ i : SixVertexSector N n, fun q : Real × Real ↦
        (q.2 • (1 : Matrix (SixVertexSector N n)
            (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n q.1) (sigma i) i by
      funext q
      simp]
    apply Finset.analyticAt_prod
    intro i _
    have hentry : AnalyticAt Real
        (fun q : Real × Real ↦
          sixVertexSectorTransfer N n q.1 (sigma i) i) z := by
      simpa only [Function.comp_apply] using
        (analyticAt_sixVertexSectorTransfer_apply N n (sigma i) i z.1).comp
          analyticAt_fst
    exact (analyticAt_snd.mul analyticAt_const).sub hentry

theorem analyticOnNhd_sixVertexSectorCharacteristicDet (N n : Nat) :
    AnalyticOnNhd Real (fun q : Real × Real ↦ Matrix.det
      (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n q.1)) Set.univ := by
  intro z _
  exact analyticAt_sixVertexSectorCharacteristicDet N n z


theorem sixVertexSectorTop_charpoly_rootMultiplicity
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    (sixVertexSectorTransfer N n c).charpoly.rootMultiplicity
      (sixVertexSectorTopEigenvalue N n hn c) = 1 := by
  let A := sixVertexSectorTransfer N n c
  let hA := sixVertexSectorTransfer_isHermitian N n c
  let T := Matrix.toEuclideanLin A
  let μ := sixVertexSectorTopEigenvalue N n hn c
  rw [← Polynomial.count_roots]
  rw [hA.roots_charpoly_eq_eigenvalues₀]
  change (Multiset.map hA.eigenvalues₀ Finset.univ.val).count μ = 1
  rw [Multiset.count_map]
  rw [← Finset.filter_val]
  change (Finset.univ.filter (fun i ↦ μ = hA.eigenvalues₀ i)).card = 1
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hcard := hT.card_filter_eigenvalues_eq finrank_euclideanSpace μ
  change (Finset.univ.filter fun i ↦ hA.eigenvalues₀ i = μ).card = _
    at hcard
  rw [show (Finset.univ.filter fun i ↦ μ = hA.eigenvalues₀ i) =
      Finset.univ.filter (fun i ↦ hA.eigenvalues₀ i = μ) by
    ext i
    simp [eq_comm]]
  rw [hcard]
  exact sixVertexSectorTop_eigenspace_finrank hn hc


theorem sixVertexSectorTop_charpoly_derivative_ne_zero
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    (sixVertexSectorTransfer N n c).charpoly.derivative.eval
      (sixVertexSectorTopEigenvalue N n hn c) ≠ 0 := by
  let p := (sixVertexSectorTransfer N n c).charpoly
  let μ := sixVertexSectorTopEigenvalue N n hn c
  have hp : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hmult : p.rootMultiplicity μ = 1 :=
    sixVertexSectorTop_charpoly_rootMultiplicity hn hc
  intro hder
  have hroot : p.IsRoot μ :=
    (Polynomial.rootMultiplicity_pos hp).mp (by rw [hmult]; omega)
  have hmultiple : 1 < p.rootMultiplicity μ :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hroot, hder⟩
  rw [hmult] at hmultiple
  omega


theorem sixVertexSectorTopEigenvalue_eq_sSup
    {N n : Nat} (hn : n ≤ N) (c : Real) :
    sixVertexSectorTopEigenvalue N n hn c = sSup
      ((fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap
          |>.reApplyInnerSelf x) '' Metric.sphere 0 1) := by
  let A := sixVertexSectorTransfer N n c
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexSectorTransfer_isHermitian N n c)
  let T' := hT.toSelfAdjoint
  let p := sixVertexPackedSector N n hn
  let e : EuclideanSpace Real (SixVertexSector N n) := EuclideanSpace.single p 1
  have he : ‖e‖ = 1 := by simp [e]
  have hsphere : (Metric.sphere
      (0 : EuclideanSpace Real (SixVertexSector N n)) 1).Nonempty :=
    ⟨e, by simp [he]⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace Real (SixVertexSector N n)) 1).exists_isMaxOn hsphere
      T'.val.reApplyInnerSelf_continuous.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  have hvne : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvnorm
    norm_num at hvnorm
  let μ : Real := T'.val.rayleighQuotient v
  have heig : Module.End.HasEigenvector T μ v := by
    have hmax' : IsMaxOn T'.val.reApplyInnerSelf (Metric.sphere 0 ‖v‖) v := by
      simpa only [hvnorm] using hmax
    exact T'.prop.hasEigenvector_of_isLocalExtrOn hvne (Or.inr hmax'.localize)
  have hmu : μ = T'.val.reApplyInnerSelf v := by
    simp [μ, ContinuousLinearMap.rayleighQuotient, hvnorm]
  have hmuEig : Module.End.HasEigenvalue T μ :=
    Module.End.hasEigenvalue_of_hasEigenvector heig
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace hmuEig
  have hμtop : μ ≤ sixVertexSectorTopEigenvalue N n hn c := by
    rw [← hi]
    exact sixVertexSectorTopEigenvalue_ge N n hn c i
  let i0 := sixVertexSectorTopIndex N n hn
  let u := hT.eigenvectorBasis finrank_euclideanSpace i0
  have hunorm : ‖u‖ = 1 :=
    hT.eigenvectorBasis finrank_euclideanSpace |>.orthonormal.1 i0
  have hu : u ∈ Metric.sphere
      (0 : EuclideanSpace Real (SixVertexSector N n)) 1 := by
    simp [hunorm]
  have huq : T'.val.reApplyInnerSelf u =
      sixVertexSectorTopEigenvalue N n hn c := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change @inner Real _ _ (T u) u = _
    rw [hT.apply_eigenvectorBasis finrank_euclideanSpace i0]
    rw [inner_smul_left, real_inner_self_eq_norm_sq, hunorm]
    simp only [one_pow, mul_one]
    change hT.eigenvalues finrank_euclideanSpace i0 =
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (sixVertexSectorTransfer_isHermitian N n c)).eigenvalues
          finrank_euclideanSpace i0
    exact congrArg (fun h : T.IsSymmetric ↦
      h.eigenvalues finrank_euclideanSpace i0) (Subsingleton.elim _ _)
  have htopmu : sixVertexSectorTopEigenvalue N n hn c ≤ μ := by
    rw [hmu, ← huq]
    exact hmax hu
  have hmueq : μ = sixVertexSectorTopEigenvalue N n hn c :=
    le_antisymm hμtop htopmu
  symm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact hsphere.image _
  · rintro y ⟨x, hx, rfl⟩
    change T'.val.reApplyInnerSelf x ≤ _
    rw [← hmueq, hmu]
    exact hmax hx
  · intro y hy
    refine ⟨T'.val.reApplyInnerSelf v, ⟨v, hv, rfl⟩, ?_⟩
    rwa [← hmu, hmueq]

theorem continuous_sixVertexSectorRayleighFamily (N n : Nat) :
    Continuous (Function.uncurry fun c : Real ↦
      fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap.reApplyInnerSelf x) := by
  rw [show (Function.uncurry fun c : Real ↦
      fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap.reApplyInnerSelf x) =
      fun q : Real × EuclideanSpace Real (SixVertexSector N n) ↦
        ∑ i, ∑ j, sixVertexSectorTransfer N n q.1 i j * q.2 j * q.2 i by
    funext q
    change
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n q.1)).toContinuousLinearMap.reApplyInnerSelf q.2 = _
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change @inner Real _ _
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n q.1) q.2) q.2 = _
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    change q.2 i * (∑ j, sixVertexSectorTransfer N n q.1 i j * q.2 j) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [continuous_iff_continuousAt]
  intro q
  have hentry (i j : SixVertexSector N n) : ContinuousAt
      (fun q : Real × EuclideanSpace Real (SixVertexSector N n) ↦
        sixVertexSectorTransfer N n q.1 i j) q :=
    (analyticAt_sixVertexSectorTransfer_apply N n i j q.1).continuousAt.comp
      continuousAt_fst
  fun_prop


theorem continuous_sixVertexSectorTopEigenvalue
    {N n : Nat} (hn : n ≤ N) :
    Continuous (sixVertexSectorTopEigenvalue N n hn) := by
  rw [show sixVertexSectorTopEigenvalue N n hn = fun c ↦ sSup
      ((fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap.reApplyInnerSelf x) ''
          Metric.sphere 0 1) by
    funext c
    exact sixVertexSectorTopEigenvalue_eq_sSup hn c]
  exact (isCompact_sphere
    (0 : EuclideanSpace Real (SixVertexSector N n)) 1).continuous_sSup
      (continuous_sixVertexSectorRayleighFamily N n)

theorem sixVertexSectorCharacteristicDet_top_eq_zero
    {N n : Nat} (hn : n ≤ N) (c : Real) :
    Matrix.det
      (sixVertexSectorTopEigenvalue N n hn c •
          (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n c) = 0 := by
  rw [show sixVertexSectorTopEigenvalue N n hn c •
      (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) =
      Matrix.scalar (SixVertexSector N n)
        (sixVertexSectorTopEigenvalue N n hn c) by
    ext i j
    simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]]
  rw [← Matrix.eval_charpoly]
  let hA := sixVertexSectorTransfer_isHermitian N n c
  apply Polynomial.IsRoot.def.mp
  have hmem : sixVertexSectorTopEigenvalue N n hn c ∈
      (sixVertexSectorTransfer N n c).charpoly.roots := by
    rw [hA.roots_charpoly_eq_eigenvalues₀]
    apply Multiset.mem_map.mpr
    exact ⟨sixVertexSectorTopIndex N n hn, by simp, rfl⟩
  exact (Polynomial.mem_roots').mp hmem |>.2

end
end StatMech.FrontierD
