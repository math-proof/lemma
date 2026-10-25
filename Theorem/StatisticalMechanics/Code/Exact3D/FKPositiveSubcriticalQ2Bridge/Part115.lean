/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part117
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem exists_boxSym_lift_positiveXFace_of_boxBoundary3
    (n : ℕ) (v : FK.boxVerts 3 n) (hv : FK.boxBoundary 3 n v) :
    ∃ S : FK.BoxSym 3, ((S.lift n v : Lattice.Site 3) 0 = (n : ℤ)) := by
  rw [FK.boxBoundary, Lattice.mem_vertexBoundary] at hv
  have hnot : ¬ ∀ i : Fin 3,
      (((v : Lattice.Site 3) i).natAbs ≤ n - 1) := hv.2
  push Not at hnot
  rcases hnot with ⟨i, hi⟩
  have hle : ((v : Lattice.Site 3) i).natAbs ≤ n := hv.1 i
  have habs : ((v : Lattice.Site 3) i).natAbs = n := by
    omega
  rcases Int.natAbs_eq_iff.mp habs with hpos | hneg
  · refine ⟨FK.rot_permBoxSym 3 (Equiv.swap (0 : Fin 3) i), ?_⟩
    simpa [FK.rot_permBoxSym, FK.rot_permEquiv_apply, Equiv.symm_swap]
      using hpos
  · refine
      ⟨boxSymComp
        (FK.rot_permBoxSym 3 (Equiv.swap (0 : Fin 3) i))
        (FK.fkTI_signFlip 3 i), ?_⟩
    simp [boxSymComp, FK.rot_permBoxSym, FK.rot_permEquiv_apply,
      Equiv.symm_swap, FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, hneg]


theorem boxBoundary3_of_positiveXFace
    {n : ℕ} (hn : 0 < n) (v : FK.boxVerts 3 n)
    (hv : (v : Lattice.Site 3) 0 = (n : ℤ)) :
    FK.boxBoundary 3 n v := by
  rw [FK.boxBoundary, Lattice.mem_vertexBoundary]
  constructor
  · exact v.property
  · rw [Lattice.mem_box]
    intro hinner
    have h0 := hinner (0 : Fin 3)
    rw [hv] at h0
    have hn_le : n ≤ n - 1 := by
      simpa using h0
    omega


theorem exists_boxSym_lift_positiveXFaceOrderedWedge_of_positiveXFace3
    (n : ℕ) (v : FK.boxVerts 3 n)
    (hv : (v : Lattice.Site 3) 0 = (n : ℤ)) :
    ∃ S : FK.BoxSym 3,
      boxVertPositiveXFaceOrderedWedge3 n (S.lift n v) := by
  let Sabs : FK.BoxSym 3 := transverseAbsBoxSym3 (v : Lattice.Site 3)
  have hSabs0 :
      ((Sabs.lift n v : Lattice.Site 3) 0 = (n : ℤ)) := by
    by_cases h1 : 0 ≤ (v : Lattice.Site 3) (1 : Fin 3)
    · by_cases h2 : 0 ≤ (v : Lattice.Site 3) (2 : Fin 3)
      · simp [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2, hv]
      · simp [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2, hv]
    · by_cases h2 : 0 ≤ (v : Lattice.Site 3) (2 : Fin 3)
      · simp [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2, hv]
      · simp [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2, hv]
  have hSabs1_nonneg :
      0 ≤ ((Sabs.lift n v : Lattice.Site 3) (1 : Fin 3)) := by
    by_cases h1 : 0 ≤ (v : Lattice.Site 3) (1 : Fin 3)
    · by_cases h2 : 0 ≤ (v : Lattice.Site 3) (2 : Fin 3)
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h1
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h1
    · have h1' : 0 ≤ -((v : Lattice.Site 3) (1 : Fin 3)) := by omega
      by_cases h2 : 0 ≤ (v : Lattice.Site 3) (2 : Fin 3)
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h1'
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h1'
  have hSabs2_nonneg :
      0 ≤ ((Sabs.lift n v : Lattice.Site 3) (2 : Fin 3)) := by
    by_cases h2 : 0 ≤ (v : Lattice.Site 3) (2 : Fin 3)
    · by_cases h1 : 0 ≤ (v : Lattice.Site 3) (1 : Fin 3)
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h2
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h2
    · have h2' : 0 ≤ -((v : Lattice.Site 3) (2 : Fin 3)) := by omega
      by_cases h1 : 0 ≤ (v : Lattice.Site 3) (1 : Fin 3)
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h2'
      · simpa [Sabs, transverseAbsBoxSym3, boxSymComp, boxSymId,
          FK.fkTI_signFlip, FK.fkTI_signFlipEquiv, h1, h2] using h2'
  by_cases hle :
      ((Sabs.lift n v : Lattice.Site 3) (1 : Fin 3) ≤
        (Sabs.lift n v : Lattice.Site 3) (2 : Fin 3))
  · refine ⟨Sabs, ?_⟩
    exact ⟨hSabs0, hSabs1_nonneg, hle⟩
  · let Sswap : FK.BoxSym 3 :=
      FK.rot_permBoxSym 3 (Equiv.swap (1 : Fin 3) (2 : Fin 3))
    refine ⟨boxSymComp Sswap Sabs, ?_⟩
    have hrev :
        (Sabs.lift n v : Lattice.Site 3) (2 : Fin 3) ≤
          (Sabs.lift n v : Lattice.Site 3) (1 : Fin 3) := by
      omega
    constructor
    · simpa [Sswap, boxSymComp, FK.rot_permBoxSym, FK.rot_permEquiv_apply,
        Equiv.symm_swap, Equiv.swap_apply_def] using hSabs0
    · constructor
      · simpa [Sswap, boxSymComp, FK.rot_permBoxSym, FK.rot_permEquiv_apply,
          Equiv.symm_swap, Equiv.swap_apply_def] using hSabs2_nonneg
      · simpa [Sswap, boxSymComp, FK.rot_permBoxSym, FK.rot_permEquiv_apply,
          Equiv.symm_swap, Equiv.swap_apply_def] using hrev


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_doubledBoxProjection
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hprojection β hβpos hβc, eventually_ge_atTop 1] with
    n hprojection_n hn
  intro v hv
  exact hprojection_n v (boxBoundary3_of_positiveXFace (by omega) v hv)


theorem freeQ2BoundaryFreeVertex_le_sameVertexDoubleScale
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n) :
    ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
      ≤
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) := by
  have hmono := FK.fkFreeLimit_monotone (d := 3) n
    (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
    (S := FK.connEvent (FK.boxGraph 3 n) (IsingFK.boxOrigin 3 n) v)
    (FK.connEvent_isIncreasing (FK.boxGraph 3 n) (IsingFK.boxOrigin 3 n) v)
  have h := hmono (Nat.zero_le n)
  simpa [FK.boxConnEvent, Nat.add_comm, two_mul] using h


theorem twoPointFun_boxSym
    {d : ℕ} (S : FK.BoxSym d) (n : ℕ) (p q : ℝ)
    (x y : FK.boxVerts d n) :
    FK.twoPointFun (FK.boxGraph d n) p q (S.lift n x) (S.lift n y) =
      FK.twoPointFun (FK.boxGraph d n) p q x y := by
  classical
  unfold FK.twoPointFun
  rw [← Equiv.sum_comp (FK.reCfgEquiv (S.lift n).symm)
    (fun η : ConfigSpace (Sym2 (FK.boxVerts d n)) =>
      FK.fkProb (FK.boxGraph d n) p q η *
        (FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y)).indicator
          (fun _ => (1 : ℝ)) η)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hsymmAdj : ∀ a b : FK.boxVerts d n,
      (FK.boxGraph d n).Adj ((S.lift n).symm a) ((S.lift n).symm b) ↔
        (FK.boxGraph d n).Adj a b := by
    intro a b
    simpa using
      (S.lift_adj n ((S.lift n).symm a) ((S.lift n).symm b)).symm
  have hprob :
      FK.fkProb (FK.boxGraph d n) p q (FK.reCfg (S.lift n).symm ω) =
        FK.fkProb (FK.boxGraph d n) p q ω := by
    exact FK.fkTI_fkProb_reCfg (FK.boxGraph d n) (S.lift n).symm
      hsymmAdj p q ω
  have hevent :
      (FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y)).indicator
          (fun _ => (1 : ℝ)) (FK.reCfg (S.lift n).symm ω) =
        (FK.connEvent (FK.boxGraph d n) x y).indicator
          (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ FK.connEvent (FK.boxGraph d n) x y
    · rw [Set.indicator_of_mem hω]
      have himg : FK.reCfg (S.lift n).symm ω ∈
          FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y) := by
        rw [FK.mem_connEvent] at hω ⊢
        let φ := FK.fkTI_openSubIso (FK.boxGraph d n) (S.lift n).symm
          hsymmAdj ω
        have hiff := SimpleGraph.Iso.reachable_iff (φ := φ)
          (u := S.lift n x) (v := S.lift n y)
        have hω' : (FK.openSub (FK.boxGraph d n) ω).Reachable
            (φ (S.lift n x)) (φ (S.lift n y)) := by
          simpa [φ, FK.fkTI_openSubIso] using hω
        exact hiff.mp hω'
      rw [Set.indicator_of_mem himg]
    · rw [Set.indicator_of_notMem hω]
      have hnot : FK.reCfg (S.lift n).symm ω ∉
          FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y) := by
        intro himg
        rw [FK.mem_connEvent] at hω himg
        let φ := FK.fkTI_openSubIso (FK.boxGraph d n) (S.lift n).symm
          hsymmAdj ω
        have hiff := SimpleGraph.Iso.reachable_iff (φ := φ)
          (u := S.lift n x) (v := S.lift n y)
        have hback := hiff.mpr himg
        exact hω (by simpa [φ, FK.fkTI_openSubIso] using hback)
      rw [Set.indicator_of_notMem hnot]
  change FK.fkProb (FK.boxGraph d n) p q (FK.reCfg (S.lift n).symm ω) *
      (FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y)).indicator
          (fun _ => (1 : ℝ)) (FK.reCfg (S.lift n).symm ω) =
    FK.fkProb (FK.boxGraph d n) p q ω *
      (FK.connEvent (FK.boxGraph d n) x y).indicator (fun _ => (1 : ℝ)) ω
  rw [hprob, hevent]


theorem freeFiniteMeasure_real_boxConnEvent_boxSym
    {d : ℕ} (S : FK.BoxSym d) (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : FK.boxVerts d n) :
    ((FK.freeFiniteMeasure d n hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n (S.lift n x) (S.lift n y))
      =
    ((FK.freeFiniteMeasure d n hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n x y) := by
  rw [FK.freeFiniteMeasure_real_boxConnEvent,
    FK.freeFiniteMeasure_real_boxConnEvent]
  exact twoPointFun_boxSym S n p q x y


theorem boxRestrictLE_reCfg_boxSym_symm
    {d n M : ℕ} (h : n ≤ M) (S : FK.BoxSym d)
    (ω : ConfigSpace (Sym2 (FK.boxVerts d M))) :
    FK.boxRestrictLE d h (FK.reCfg (S.lift M).symm ω) =
      FK.reCfg (S.lift n).symm (FK.boxRestrictLE d h ω) := by
  funext e
  unfold FK.boxRestrictLE FK.reCfg
  congr 1
  induction e using Sym2.ind with
  | _ a b =>
      have ha :
          (S.lift M).symm (FK.boxVertInclLE d h a) =
            FK.boxVertInclLE d h ((S.lift n).symm a) := by
        apply (S.lift M).injective
        simpa using (S.lift_boxVertInclLE h ((S.lift n).symm a)).symm
      have hb :
          (S.lift M).symm (FK.boxVertInclLE d h b) =
            FK.boxVertInclLE d h ((S.lift n).symm b) := by
        apply (S.lift M).injective
        simpa using (S.lift_boxVertInclLE h ((S.lift n).symm b)).symm
      simp [FK.innerEdgeLE, ha, hb]


theorem freeFiniteMeasure_real_innerBoxConnEvent_boxSym
    {d n M : ℕ} (h : n ≤ M) (S : FK.BoxSym d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : FK.boxVerts d n) :
    ((FK.freeFiniteMeasure d M hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n (S.lift n x) (S.lift n y))
      =
    ((FK.freeFiniteMeasure d M hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n x y) := by
  classical
  let T₁ : Set (ConfigSpace (Sym2 (FK.boxVerts d M))) :=
    FK.boxRestrictLE d h ⁻¹'
      FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y)
  let T₀ : Set (ConfigSpace (Sym2 (FK.boxVerts d M))) :=
    FK.boxRestrictLE d h ⁻¹' FK.connEvent (FK.boxGraph d n) x y
  have hmeas₁ : MeasurableSet (FK.boxRestrict d M ⁻¹' T₁) :=
    (FK.continuous_boxRestrict d M).measurable (MeasurableSet.of_discrete)
  have hmeas₀ : MeasurableSet (FK.boxRestrict d M ⁻¹' T₀) :=
    (FK.continuous_boxRestrict d M).measurable (MeasurableSet.of_discrete)
  have hevent₁ :
      FK.boxConnEvent d n (S.lift n x) (S.lift n y) =
        FK.boxRestrict d M ⁻¹' T₁ := by
    ext ω
    simp [T₁, FK.boxConnEvent, FK.boxRestrictLE_boxRestrict]
  have hevent₀ :
      FK.boxConnEvent d n x y = FK.boxRestrict d M ⁻¹' T₀ := by
    ext ω
    simp [T₀, FK.boxConnEvent, FK.boxRestrictLE_boxRestrict]
  rw [hevent₁,
    FK.freeFiniteMeasure_real_boxRestrictEvent M hp hp1 hq T₁ hmeas₁,
    hevent₀,
    FK.freeFiniteMeasure_real_boxRestrictEvent M hp hp1 hq T₀ hmeas₀]
  rw [← Equiv.sum_comp (FK.reCfgEquiv (S.lift M).symm)
    (fun η : ConfigSpace (Sym2 (FK.boxVerts d M)) =>
      T₁.indicator (fun _ => (1 : ℝ)) η *
        FK.fkProb (FK.boxGraph d M) p q η)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hsymmAdj : ∀ a b : FK.boxVerts d M,
      (FK.boxGraph d M).Adj ((S.lift M).symm a) ((S.lift M).symm b) ↔
        (FK.boxGraph d M).Adj a b := by
    intro a b
    simpa using
      (S.lift_adj M ((S.lift M).symm a) ((S.lift M).symm b)).symm
  have hprob :
      FK.fkProb (FK.boxGraph d M) p q (FK.reCfg (S.lift M).symm ω) =
        FK.fkProb (FK.boxGraph d M) p q ω := by
    exact FK.fkTI_fkProb_reCfg (FK.boxGraph d M) (S.lift M).symm
      hsymmAdj p q ω
  have hevent :
      T₁.indicator (fun _ => (1 : ℝ)) (FK.reCfg (S.lift M).symm ω) =
        T₀.indicator (fun _ => (1 : ℝ)) ω := by
    have hrestrict := boxRestrictLE_reCfg_boxSym_symm h S ω
    by_cases hω : FK.boxRestrictLE d h ω ∈
        FK.connEvent (FK.boxGraph d n) x y
    · rw [Set.indicator_of_mem (show ω ∈ T₀ from hω)]
      have himg : FK.reCfg (S.lift M).symm ω ∈ T₁ := by
        change FK.boxRestrictLE d h (FK.reCfg (S.lift M).symm ω) ∈
          FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y)
        rw [hrestrict]
        rw [FK.mem_connEvent] at hω ⊢
        have hsymmAdjInner : ∀ a b : FK.boxVerts d n,
            (FK.boxGraph d n).Adj ((S.lift n).symm a) ((S.lift n).symm b) ↔
              (FK.boxGraph d n).Adj a b := by
          intro a b
          simpa using
            (S.lift_adj n ((S.lift n).symm a) ((S.lift n).symm b)).symm
        let φ := FK.fkTI_openSubIso (FK.boxGraph d n) (S.lift n).symm
          hsymmAdjInner (FK.boxRestrictLE d h ω)
        have hiff := SimpleGraph.Iso.reachable_iff (φ := φ)
          (u := S.lift n x) (v := S.lift n y)
        have hω' : (FK.openSub (FK.boxGraph d n)
            (FK.boxRestrictLE d h ω)).Reachable
            (φ (S.lift n x)) (φ (S.lift n y)) := by
          simpa [φ, FK.fkTI_openSubIso] using hω
        exact hiff.mp hω'
      rw [Set.indicator_of_mem himg]
    · rw [Set.indicator_of_notMem (show ω ∉ T₀ from hω)]
      have hnot : FK.reCfg (S.lift M).symm ω ∉ T₁ := by
        intro himg
        have himg' :
            FK.reCfg (S.lift n).symm (FK.boxRestrictLE d h ω) ∈
              FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y) := by
          change FK.boxRestrictLE d h (FK.reCfg (S.lift M).symm ω) ∈
            FK.connEvent (FK.boxGraph d n) (S.lift n x) (S.lift n y) at himg
          rwa [hrestrict] at himg
        rw [FK.mem_connEvent] at hω himg'
        have hsymmAdjInner : ∀ a b : FK.boxVerts d n,
            (FK.boxGraph d n).Adj ((S.lift n).symm a) ((S.lift n).symm b) ↔
              (FK.boxGraph d n).Adj a b := by
          intro a b
          simpa using
            (S.lift_adj n ((S.lift n).symm a) ((S.lift n).symm b)).symm
        let φ := FK.fkTI_openSubIso (FK.boxGraph d n) (S.lift n).symm
          hsymmAdjInner (FK.boxRestrictLE d h ω)
        have hiff := SimpleGraph.Iso.reachable_iff (φ := φ)
          (u := S.lift n x) (v := S.lift n y)
        have hback := hiff.mpr himg'
        exact hω (by simpa [φ, FK.fkTI_openSubIso] using hback)
      rw [Set.indicator_of_notMem hnot]
  change T₁.indicator (fun _ => (1 : ℝ)) (FK.reCfg (S.lift M).symm ω) *
      FK.fkProb (FK.boxGraph d M) p q (FK.reCfg (S.lift M).symm ω) =
    T₀.indicator (fun _ => (1 : ℝ)) ω *
      FK.fkProb (FK.boxGraph d M) p q ω
  rw [hevent, hprob]


theorem boxSym_fixes_origin {d : ℕ} (S : FK.BoxSym d) :
    S.τ (StatMech.Percolation.origin d) =
      StatMech.Percolation.origin d := by
  have h0 : S.τ (StatMech.Percolation.origin d) ∈ Lattice.box d 0 :=
    (S.box_mem 0 (StatMech.Percolation.origin d)).mpr
      (fun i => by simp [StatMech.Percolation.origin])
  funext i
  have hi : (S.τ (StatMech.Percolation.origin d) i).natAbs ≤ 0 := h0 i
  have hzero : (S.τ (StatMech.Percolation.origin d) i).natAbs = 0 :=
    Nat.le_zero.mp hi
  simpa [StatMech.Percolation.origin] using Int.natAbs_eq_zero.mp hzero


theorem boxSym_lift_boxOrigin {d : ℕ} (S : FK.BoxSym d) (n : ℕ) :
    S.lift n (IsingFK.boxOrigin d n) = IsingFK.boxOrigin d n := by
  apply Subtype.ext
  exact boxSym_fixes_origin S


theorem freeFiniteMeasure_real_boxOriginConnEvent_boxSym
    {d : ℕ} (S : FK.BoxSym d) (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (y : FK.boxVerts d n) :
    ((FK.freeFiniteMeasure d n hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n (IsingFK.boxOrigin d n) (S.lift n y))
      =
    ((FK.freeFiniteMeasure d n hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n (IsingFK.boxOrigin d n) y) := by
  have h := freeFiniteMeasure_real_boxConnEvent_boxSym S n hp hp1 hq
    (IsingFK.boxOrigin d n) y
  simpa [boxSym_lift_boxOrigin] using h


theorem freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym
    {d n M : ℕ} (h : n ≤ M) (S : FK.BoxSym d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (y : FK.boxVerts d n) :
    ((FK.freeFiniteMeasure d M hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n (IsingFK.boxOrigin d n) (S.lift n y))
      =
    ((FK.freeFiniteMeasure d M hp hp1 hq)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d n (IsingFK.boxOrigin d n) y) := by
  have hsym := freeFiniteMeasure_real_innerBoxConnEvent_boxSym h S hp hp1 hq
    (IsingFK.boxOrigin d n) y
  simpa [boxSym_lift_boxOrigin] using hsym


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_positiveXFaceOrderedWedge
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hprojection β hβpos hβc] with n hprojection_n
  intro v hv
  rcases exists_boxSym_lift_positiveXFaceOrderedWedge_of_positiveXFace3 n v hv with
    ⟨S, hS⟩
  have hsym := freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym
    (d := 3) (n := n) (M := 2 * n) (by omega) S
    (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
    (by norm_num : (0 : ℝ) < 2) v
  calc
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        =
      ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) (S.lift n v)) := by
        exact hsym.symm
    _ ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n :=
        hprojection_n (S.lift n v) hS


theorem freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFace
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hprojection β hβpos hβc] with n hprojection_n
  intro v hv
  rcases exists_boxSym_lift_positiveXFace_of_boxBoundary3 n v hv with ⟨S, hS⟩
  have hsym := freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym
    (d := 3) (n := n) (M := 2 * n) (by omega) S
    (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
    (by norm_num : (0 : ℝ) < 2) v
  calc
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        =
      ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) (S.lift n v)) := by
        exact hsym.symm
    _ ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n :=
        hprojection_n (S.lift n v) hS


theorem freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedge
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFace
    (freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_positiveXFaceOrderedWedge
      hprojection)


theorem freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_doubledBoxProjection
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical := by
  intro β hβpos hβc
  refine ⟨1, 0, by norm_num, ?_⟩
  filter_upwards [hprojection β hβpos hβc] with n hprojection_n
  intro v hv
  simpa using hprojection_n v hv


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjectionPositiveSubcritical := by
  intro β hβpos hβc
  rcases hprojection β hβpos hβc with ⟨C, k, hC, hprojectionHi⟩
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [hprojectionHi] with n hprojection_n
  intro v hv
  rcases exists_boxSym_lift_positiveXFaceOrderedWedge_of_positiveXFace3 n v hv with
    ⟨S, hS⟩
  have hsym := freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym
    (d := 3) (n := n) (M := 2 * n) (by omega) S
    (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
    (by norm_num : (0 : ℝ) < 2) v
  calc
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        =
      ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) (S.lift n v)) := by
        exact hsym.symm
    _ ≤ C * (n : ℝ) ^ k *
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
            (2 * n) n :=
        hprojection_n (S.lift n v) hS


theorem freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFace
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical := by
  intro β hβpos hβc
  rcases hprojection β hβpos hβc with ⟨C, k, hC, hprojectionHi⟩
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [hprojectionHi] with n hprojection_n
  intro v hv
  rcases exists_boxSym_lift_positiveXFace_of_boxBoundary3 n v hv with ⟨S, hS⟩
  have hsym := freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym
    (d := 3) (n := n) (M := 2 * n) (by omega) S
    (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
    (by norm_num : (0 : ℝ) < 2) v
  calc
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        =
      ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) (S.lift n v)) := by
        exact hsym.symm
    _ ≤ C * (n : ℝ) ^ k *
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
            (2 * n) n :=
        hprojection_n (S.lift n v) hS


theorem
    freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFace
    (freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge
      hprojection)


theorem freeQ2BoundaryFreeVertexDoubleScaleProjection_of_doubledBoxProjection
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hprojection β hβpos hβc] with n hprojection_n
  intro v hv
  exact le_trans
    (freeQ2BoundaryFreeVertex_le_sameVertexDoubleScale β hβpos n v)
    (hprojection_n v hv)


theorem freeQ2BoundaryFreeVertexDoubleScaleProjection_xAxis
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) :
    ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n)
          (ising3DXAxisBoxVertex n))
      ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n := by
  have horigin : ising3DOriginBoxVertex n = IsingFK.boxOrigin 3 n := by
    ext
    rfl
  rw [← horigin]
  exact freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer
    β hβpos (n := n) (M₁ := n) (M₂ := 2 * n)
    (Nat.le_refl n) (by omega)


theorem freeQ2BoundaryFreeVertexDoubleScaleProjection_of_boxSym_xAxis
    (β : ℝ) (hβpos : 0 < β) (n : ℕ)
    (v : FK.boxVerts 3 n) (S : FK.BoxSym 3)
    (hv : S.lift n v = ising3DXAxisBoxVertex n) :
    ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
      ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n := by
  have hsym := freeFiniteMeasure_real_boxOriginConnEvent_boxSym S n
    (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
    (by norm_num : (0 : ℝ) < 2) v
  calc
    ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        =
      ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n)
          (ising3DXAxisBoxVertex n)) := by
        simpa [hv] using hsym.symm
    _ ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n :=
        freeQ2BoundaryFreeVertexDoubleScaleProjection_xAxis β hβpos n


theorem freeQ2BoundaryFreeVertexDoubledBoxProjection_xAxis
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) :
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n)
          (ising3DXAxisBoxVertex n))
      ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n := by
  have horigin : ising3DOriginBoxVertex n = IsingFK.boxOrigin 3 n := by
    ext
    rfl
  rw [freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume, horigin]


theorem boxVert_eq_xAxis_of_positiveXFaceOrderedWedge_height_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v = 0) :
    v = ising3DXAxisBoxVertex n := by
  rcases Nat.add_eq_zero.mp hheight with ⟨hyabs, hzabs⟩
  have hy : (v : Lattice.Site 3) (1 : Fin 3) = 0 :=
    Int.natAbs_eq_zero.mp hyabs
  have hz : (v : Lattice.Site 3) (2 : Fin 3) = 0 :=
    Int.natAbs_eq_zero.mp hzabs
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [ising3DXAxisBoxVertex, ising3DXAxisRay, ising3DSiteOfCoords,
      hv.1, hy, hz]


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescent_of_coordinateStep
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescentDoubledBoxProjectionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hstep β hβpos hβc] with n hstep_n
  intro v hvwedge hheight
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  have hy_nonneg : 0 ≤ y := by
    simpa [y] using hvwedge.2.1
  have hy_le_z : y ≤ z := by
    simpa [y, z] using hvwedge.2.2
  by_cases hlt : y < z
  · have hcase :
        ∃ w : FK.boxVerts 3 n,
          boxVertHasCoords3 w (n : ℤ) y (z - 1) ∧
            ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
              ≤
            ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w) := by
      simpa only [y, z, hlt, if_true] using hstep_n v hvwedge hheight
    rcases hcase with ⟨w, hwcoords, hprob⟩
    refine ⟨w, ?_, ?_, hprob⟩
    · rcases hwcoords with ⟨hw0, hw1, hw2⟩
      refine ⟨hw0, ?_, ?_⟩
      · rw [hw1]
        exact hy_nonneg
      · rw [hw1, hw2]
        omega
    · rcases hwcoords with ⟨_hw0, hw1, hw2⟩
      have hz_minus_nonneg : 0 ≤ z - 1 := by
        omega
      have hzm_lt_z : (z - 1).natAbs < z.natAbs :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt hz_minus_nonneg (by omega)
      calc
        boxVertTransverseHeight3 w = y.natAbs + (z - 1).natAbs := by
          simp [boxVertTransverseHeight3, y, z, hw1, hw2]
        _ < y.natAbs + z.natAbs := Nat.add_lt_add_left hzm_lt_z _
        _ = boxVertTransverseHeight3 v := by
          simp [boxVertTransverseHeight3, y, z]
  · have hcase :
        ∃ w : FK.boxVerts 3 n,
          boxVertHasCoords3 w (n : ℤ) (y - 1) z ∧
            ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
              ≤
            ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w) := by
      simpa only [y, z, hlt, if_false] using hstep_n v hvwedge hheight
    rcases hcase with ⟨w, hwcoords, hprob⟩
    have hdiag : y = z := by
      omega
    have hy_ne_zero : y ≠ 0 := by
      intro hy0
      have hz0 : z = 0 := by
        omega
      apply hheight
      simp [boxVertTransverseHeight3, y, z, hy0, hz0]
    have hy_pos : 0 < y := by
      omega
    refine ⟨w, ?_, ?_, hprob⟩
    · rcases hwcoords with ⟨hw0, hw1, hw2⟩
      refine ⟨hw0, ?_, ?_⟩
      · rw [hw1]
        omega
      · rw [hw1, hw2]
        omega
    · rcases hwcoords with ⟨_hw0, hw1, hw2⟩
      have hy_minus_nonneg : 0 ≤ y - 1 := by
        omega
      have hym_lt_y : (y - 1).natAbs < y.natAbs :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt hy_minus_nonneg (by omega)
      calc
        boxVertTransverseHeight3 w = (y - 1).natAbs + z.natAbs := by
          simp [boxVertTransverseHeight3, y, z, hw1, hw2]
        _ < y.natAbs + z.natAbs := Nat.add_lt_add_right hym_lt_y _
        _ = boxVertTransverseHeight3 v := by
          simp [boxVertTransverseHeight3, y, z]


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_strictDescent
    (hdescent :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescentDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hdescent β hβpos hβc] with n hdescent_n
  intro v hvwedge
  let P : FK.boxVerts 3 n → ℝ := fun u =>
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) u)
  let B := freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n
  have hclaim : ∀ k : ℕ, ∀ u : FK.boxVerts 3 n,
      boxVertTransverseHeight3 u = k →
        boxVertPositiveXFaceOrderedWedge3 n u → P u ≤ B := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro u huk huwedge
        by_cases hk0 : k = 0
        · have huAxis :
            u = ising3DXAxisBoxVertex n :=
              boxVert_eq_xAxis_of_positiveXFaceOrderedWedge_height_zero
                huwedge (by omega)
          rw [huAxis]
          simpa [P, B] using
            freeQ2BoundaryFreeVertexDoubledBoxProjection_xAxis β hβpos n
        · have huheight_ne : boxVertTransverseHeight3 u ≠ 0 := by
            omega
          rcases hdescent_n u huwedge huheight_ne with ⟨w, hwwedge, hlt, hstep⟩
          have hPw : P w ≤ B :=
            ih (boxVertTransverseHeight3 w) (by simpa [huk] using hlt) w rfl
              hwwedge
          exact le_trans (by simpa [P] using hstep) hPw
  exact hclaim (boxVertTransverseHeight3 v) v rfl hvwedge


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_coordinateStep
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_strictDescent
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescent_of_coordinateStep
      hstep)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_additiveStrictDescentPolynomialError
    (hdescent :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialErrorPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical := by
  intro β hβpos hβc
  rcases hdescent β hβpos hβc with ⟨C, k, hC, hdescentHi⟩
  refine ⟨1 + 2 * C, k + 1, by positivity, ?_⟩
  filter_upwards [hdescentHi, eventually_ge_atTop 1] with n hdescent_n hn
  intro v hvwedge
  let B := freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n
  let E := C * (n : ℝ) ^ k * B
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume]
    exact measureReal_nonneg
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact
      mul_nonneg
        (mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg n) k))
        hB_nonneg
  let P : FK.boxVerts 3 n → ℝ := fun u =>
    freeQ2DoubledInnerOriginConnProb β hβpos n u
  have hclaim : ∀ m : ℕ, ∀ u : FK.boxVerts 3 n,
      boxVertTransverseHeight3 u = m →
        boxVertPositiveXFaceOrderedWedge3 n u →
          P u ≤ B + (m : ℝ) * E := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro u hum huwedge
        by_cases hm0 : m = 0
        · have huAxis : u = ising3DXAxisBoxVertex n :=
            boxVert_eq_xAxis_of_positiveXFaceOrderedWedge_height_zero
              huwedge (by omega)
          have haxis : P u ≤ B := by
            rw [huAxis]
            simpa [P, B, freeQ2DoubledInnerOriginConnProb] using
              freeQ2BoundaryFreeVertexDoubledBoxProjection_xAxis
                β hβpos n
          have hterm_nonneg : 0 ≤ (m : ℝ) * E :=
            mul_nonneg (Nat.cast_nonneg m) hE_nonneg
          linarith
        · have huheight_ne : boxVertTransverseHeight3 u ≠ 0 := by
            omega
          rcases hdescent_n u huwedge huheight_ne with
            ⟨w, hwwedge, hlt, hstep⟩
          have hPw : P w ≤
              B + (boxVertTransverseHeight3 w : ℝ) * E :=
            ih (boxVertTransverseHeight3 w)
              (by simpa [hum] using hlt) w rfl hwwedge
          have hsucc_le :
              (boxVertTransverseHeight3 w : ℝ) + 1 ≤ (m : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt (by simpa [hum] using hlt)
          have htail :
              (boxVertTransverseHeight3 w : ℝ) * E + E ≤
                (m : ℝ) * E := by
            calc
              (boxVertTransverseHeight3 w : ℝ) * E + E =
                  ((boxVertTransverseHeight3 w : ℝ) + 1) * E := by
                    ring
              _ ≤ (m : ℝ) * E :=
                mul_le_mul_of_nonneg_right hsucc_le hE_nonneg
          calc
            P u ≤ P w + E := by
              simpa [P, E] using hstep
            _ ≤ (B + (boxVertTransverseHeight3 w : ℝ) * E) + E := by
              linarith
            _ = B + ((boxVertTransverseHeight3 w : ℝ) * E + E) := by
              ring
            _ ≤ B + (m : ℝ) * E := by
              linarith
  have hv_bound :
      (boxVertTransverseHeight3 v : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast boxVertTransverseHeight3_le_two_mul v
  have hv_est :
      P v ≤ B + (boxVertTransverseHeight3 v : ℝ) * E :=
    hclaim (boxVertTransverseHeight3 v) v rfl hvwedge
  have hto_two :
      B + (boxVertTransverseHeight3 v : ℝ) * E ≤
        B + (2 * (n : ℝ)) * E := by
    have hmul := mul_le_mul_of_nonneg_right hv_bound hE_nonneg
    linarith
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (k + 1) :=
    one_le_pow₀ hn_real
  have hB_le : B ≤ (n : ℝ) ^ (k + 1) * B := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hpow hB_nonneg
  have hE_eq :
      (2 * (n : ℝ)) * E =
        (2 * C * (n : ℝ) ^ (k + 1)) * B := by
    dsimp [E]
    rw [pow_succ']
    ring
  calc
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        = P v := by
          rfl
    _ ≤ B + (boxVertTransverseHeight3 v : ℝ) * E := hv_est
    _ ≤ B + (2 * (n : ℝ)) * E := hto_two
    _ ≤ (n : ℝ) ^ (k + 1) * B +
          (2 * C * (n : ℝ) ^ (k + 1)) * B := by
        exact add_le_add hB_le (le_of_eq hE_eq)
    _ = (1 + 2 * C) * (n : ℝ) ^ (k + 1) * B := by
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullStrictDescent_detourPolynomialBound
    (hfull :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical)
    (hdetour :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_additiveStrictDescentPolynomialError
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialError_of_fullStrictDescent_detourPolynomialBound
      hfull hdetour)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_detourPolynomialBound
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hdetour :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullStrictDescent_detourPolynomialBound
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullPredecessorComparisons
      hstrict hdiag)
    hdetour

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_profileDoubleScale
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_detourPolynomialBound
    hstrict hdiag
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBound_of_profileDoubleScale
      hprofile)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullCoordinateComparisons_profileDoubleScale
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_profileDoubleScale
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparison_of_fullCoordinateComparison
      hstrict)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparison_of_fullCoordinateComparison
      hdiag)
    hprofile


theorem freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeStrictDescent
    (hdescent :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescentDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedge
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_strictDescent
      hdescent)


theorem freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeCoordinateStep
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedge
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_coordinateStep
      hstep)


theorem freeQ2BoundaryFreeVertexDoubledBoxProjection_of_boxSym_xAxis
    (β : ℝ) (hβpos : 0 < β) (n : ℕ)
    (v : FK.boxVerts 3 n) (S : FK.BoxSym 3)
    (hv : S.lift n v = ising3DXAxisBoxVertex n) :
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
      ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n := by
  have hsym := freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym
    (d := 3) (n := n) (M := 2 * n) (by omega) S
    (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
    (by norm_num : (0 : ℝ) < 2) v
  calc
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        =
      ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n)
          (ising3DXAxisBoxVertex n)) := by
        simpa [hv] using hsym.symm
    _ ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
          (2 * n) n :=
        freeQ2BoundaryFreeVertexDoubledBoxProjection_xAxis β hβpos n

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileDoubleScaleAt_of_simonFreeSumAt_projectionAt
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionAt β hβpos n) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n := by
  let B := freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n
  have hsum :
      (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v))
        ≤ ∑ _v ∈ Finset.univ.filter (FK.boxBoundary 3 n), B := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact hprojection v (by simpa using hv)
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) :=
      hsimon
    _ ≤ ∑ _v ∈ Finset.univ.filter (FK.boxBoundary 3 n), B :=
      hsum
    _ =
        ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
            (2 * n) n := by
      simp [B, nsmul_eq_mul]

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_simonFreeSumAt_projectionAt
    (hsimon :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n)
    (hprojection :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          FreeQ2BoundaryFreeVertexDoubleScaleProjectionAt β hβpos n) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hsimon β hβpos hβc, hprojection β hβpos hβc] with
    n hsimon_n hprojection_n
  exact freeQ2BoundaryProfileDoubleScaleAt_of_simonFreeSumAt_projectionAt
    hsimon_n hprojection_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_finiteFKAt_projectionAt
    (hfinite :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n)
    (hprojection :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          FreeQ2BoundaryFreeVertexDoubleScaleProjectionAt β hβpos n) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_simonFreeSumAt_projectionAt
    (fun β hβpos hβc => by
      filter_upwards [hfinite β hβpos hβc] with n hfinite_n
      exact freeQ2BoundaryProfileSimonFreeSumAt_of_finiteFKAt hfinite_n)
    hprojection


theorem freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hsimon β hβpos hβc, hprojection β hβpos hβc] with
    n hsimon_n hprojection_n
  let B := freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n
  have hsum :
      (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v))
        ≤ ∑ _v ∈ Finset.univ.filter (FK.boxBoundary 3 n), B := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact hprojection_n v (by simpa using hv)
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) :=
      hsimon_n
    _ ≤ ∑ _v ∈ Finset.univ.filter (FK.boxBoundary 3 n), B :=
      hsum
    _ =
        ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
            (2 * n) n := by
      simp [B, nsmul_eq_mul]


theorem freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection hsimon
    (freeQ2BoundaryFreeVertexDoubleScaleProjection_of_doubledBoxProjection
      hprojection)


theorem freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection hsimon
    (freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFace hprojection)


theorem
    freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection hsimon
    (freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_positiveXFaceOrderedWedge
      hprojection)


theorem
    freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
    hsimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_coordinateStep
      hstep)


theorem freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_projection
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite) hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_doubledBoxProjection
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite) hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceProjection
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite) hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite) hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite) hstep


theorem freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_projection
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_projection
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_doubledBoxProjection
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_doubledBoxProjection
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceProjection
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceProjection
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hstep


theorem freeQ2BoundaryProfileDoubleScale_of_vertexDoubleScale
    (hcompare :
      FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcompare β hβpos hβc] with n hpoint_n
  exact freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβpos n
    (fun v hv => hpoint_n v hv)


theorem freeQ2BoundaryVertexScaledPolynomial_of_doubleScale
    (hcompare :
      FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryVertexScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  refine ⟨fun n => 2 * n, 1, 0, by norm_num, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 0] with n _hn
    omega
  · filter_upwards [hcompare β hβpos hβc] with n hpoint_n
    intro v hv
    have hpoint := hpoint_n v hv
    simpa using hpoint


theorem
    freeQ2BoundaryVertexFiniteVolumeComparisonToXAxis_of_finiteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨C, k, hC, hcompareHi⟩
  refine
    ⟨fun n : ℕ => C * (n : ℝ) ^ k,
      PositiveSubexponentialPrefactor.const_mul hC
        (PositiveSubexponentialPrefactor.natCast_pow k), ?_⟩
  filter_upwards [hcompareHi] with n hcompare_n
  intro v hv
  exact hcompare_n v hv


theorem
    freeQ2BoundaryProfileFiniteVolumeComparison_of_boundaryVertexFiniteVolume
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨Aratio, hAratio, hpointHi⟩
  refine
    ⟨fun n =>
      ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * Aratio n,
      boxBoundaryCard3_mul_positiveSubexponentialPrefactor hAratio, ?_⟩
  filter_upwards [hpointHi] with n hpoint_n
  classical
  have hpoint_all :
      ∀ᶠ M in atTop,
        ∀ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
            ≤ Aratio n *
              freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n := by
    rw [Filter.eventually_all_finset
      (Finset.univ.filter (FK.boxBoundary 3 n))]
    intro v hv
    exact hpoint_n v (by simpa using hv)
  filter_upwards [hpoint_all] with M hpoint_M
  have hprofile :
      freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (Aratio n *
            freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n) :=
    freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβpos n
      (fun v hv => hpoint_M v (by simpa using hv))
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (Aratio n *
            freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n) :=
      hprofile
    _ =
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * Aratio n) *
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n := by
      ring


theorem
    freeQ2BoundaryProfileFiniteVolumePolynomial_of_boundaryVertexPolynomial
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨C, k, hC, hpointHi⟩
  refine ⟨26 * C, k + 2, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards
    [boxBoundaryCard3_eventually_le_26_mul_sq, hpointHi,
      eventually_ge_atTop 1] with n hcard hpoint_n hn
  classical
  have hpoint_all :
      ∀ᶠ M in atTop,
        ∀ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
            ≤ C * (n : ℝ) ^ k *
              freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
                β hβpos M n := by
    rw [Filter.eventually_all_finset
      (Finset.univ.filter (FK.boxBoundary 3 n))]
    intro v hv
    exact hpoint_n v (by simpa using hv)
  filter_upwards [hpoint_all] with M hpoint_M
  let x := freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume]
    exact measureReal_nonneg
  have hpoly_nonneg : 0 ≤ C * (n : ℝ) ^ k :=
    mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg n) k)
  have hcoeff :
      ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k) ≤
        (26 * (n : ℝ) ^ 2) * (C * (n : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_right hcard hpoly_nonneg
  have hprofile :
      freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k * x) :=
    freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβpos n
      (fun v hv => hpoint_M v (by simpa using hv))
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k * x) :=
      hprofile
    _ =
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k)) * x := by
      ring
    _ ≤
        ((26 * (n : ℝ) ^ 2) * (C * (n : ℝ) ^ k)) * x :=
      mul_le_mul_of_nonneg_right hcoeff hx_nonneg
    _ =
        26 * C * (n : ℝ) ^ (k + 2) * x := by
      rw [pow_add]
      ring


theorem
    freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexScaledPolynomial
    (hcompare :
      FreeQ2BoundaryVertexScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with
    ⟨outerScale, C, k, hC, houter, hpointHi⟩
  refine ⟨outerScale, 26 * C, k + 2, mul_pos (by norm_num) hC, houter, ?_⟩
  filter_upwards
    [boxBoundaryCard3_eventually_le_26_mul_sq, hpointHi,
      eventually_ge_atTop 1] with n hcard hpoint_n hn
  let x :=
    freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (outerScale n) n
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume]
    exact measureReal_nonneg
  have hpoly_nonneg : 0 ≤ C * (n : ℝ) ^ k :=
    mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg n) k)
  have hcoeff :
      ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k) ≤
        (26 * (n : ℝ) ^ 2) * (C * (n : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_right hcard hpoly_nonneg
  have hprofile :
      freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k * x) :=
    freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβpos n
      (fun v hv => hpoint_n v hv)
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k * x) :=
      hprofile
    _ =
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          (C * (n : ℝ) ^ k)) * x := by
      ring
    _ ≤
        ((26 * (n : ℝ) ^ 2) * (C * (n : ℝ) ^ k)) * x :=
      mul_le_mul_of_nonneg_right hcoeff hx_nonneg
    _ =
        26 * C * (n : ℝ) ^ (k + 2) * x := by
      rw [pow_add]
      ring


theorem freeQ2BoundaryProfileScaledPolynomial_of_vertexDoubleScale
    (hcompare :
      FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexScaledPolynomial
    (freeQ2BoundaryVertexScaledPolynomial_of_doubleScale hcompare)


theorem freeQ2BoundaryProfileScaledPolynomial_of_profileDoubleScale
    (hcompare :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  refine ⟨fun n => 2 * n, 26, 2, by norm_num, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 0] with n _hn
    omega
  · filter_upwards
      [hcompare β hβpos hβc, boxBoundaryCard3_eventually_le_26_mul_sq]
      with n hprofile hcard
    let x :=
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n
    have hx_nonneg : 0 ≤ x := by
      dsimp [x, freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume]
      exact measureReal_nonneg
    calc
      freeQ2BoundaryProfileOfBeta β hβpos n
          ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * x := by
        simpa [x] using hprofile
      _ ≤ (26 * (n : ℝ) ^ 2) * x :=
        mul_le_mul_of_nonneg_right hcard hx_nonneg
      _ = 26 * (n : ℝ) ^ 2 * x := by ring


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hprojection β hβpos hβc with ⟨C, k, hC, hprojectionHi⟩
  refine ⟨fun n => 2 * n, 26 * C, k + 2, mul_pos (by norm_num) hC, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 0] with n _hn
    omega
  · filter_upwards
      [hsimon β hβpos hβc, hprojectionHi,
        boxBoundaryCard3_eventually_le_26_mul_sq] with
      n hsimon_n hprojection_n hcard
    classical
    let x :=
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n
    have hx_nonneg : 0 ≤ x := by
      dsimp [x, freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume]
      exact measureReal_nonneg
    have hpoly_nonneg : 0 ≤ C * (n : ℝ) ^ k :=
      mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg n) k)
    have hcoeff :
        ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            (C * (n : ℝ) ^ k) ≤
          (26 * (n : ℝ) ^ 2) * (C * (n : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hcard hpoly_nonneg
    have hsum :
        (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
                (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v))
          ≤ ∑ _v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
              C * (n : ℝ) ^ k * x := by
      refine Finset.sum_le_sum ?_
      intro v hv
      exact le_trans
        (freeQ2BoundaryFreeVertex_le_sameVertexDoubleScale β hβpos n v)
        (by
          simpa [x] using hprojection_n v (by simpa using hv))
    calc
      freeQ2BoundaryProfileOfBeta β hβpos n
          ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
                (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) :=
        hsimon_n
      _ ≤ ∑ _v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            C * (n : ℝ) ^ k * x :=
        hsum
      _ =
          ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            (C * (n : ℝ) ^ k * x) := by
        simp [nsmul_eq_mul]
      _ =
          (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            (C * (n : ℝ) ^ k)) * x := by
        ring
      _ ≤ ((26 * (n : ℝ) ^ 2) * (C * (n : ℝ) ^ k)) * x :=
        mul_le_mul_of_nonneg_right hcoeff hx_nonneg
      _ =
          26 * C * (n : ℝ) ^ (k + 2) * x := by
        rw [pow_add]
        ring


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite) hprojection


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection
    hsimon
    (freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge
      hprojection)


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite) hprojection


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_doubledBoxPolynomialProjection
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    hsimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullCoordinateComparisons_profileDoubleScale
      hstrict hdiag hprofile)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite)
    hstrict hdiag hprofile

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hstrict hdiag hprofile


theorem
    freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexPolynomial
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_finiteVolumePolynomial
    (freeQ2BoundaryProfileFiniteVolumePolynomial_of_boundaryVertexPolynomial
      hcompare)


theorem
    freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_boundaryVertexPolynomial
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileFiniteVolumePolynomial
    (freeQ2BoundaryProfileFiniteVolumePolynomial_of_boundaryVertexPolynomial
      hcompare)


theorem
    freeQ2BoundaryVertexSubexpComparisonToXAxis_of_finiteVolumeComparison
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨Aratio, hAratio, hcompareHi⟩
  refine ⟨Aratio, hAratio, ?_⟩
  filter_upwards [hcompareHi] with n hcompare_n
  intro v hv
  have hlim :
      Tendsto
        (fun M : ℕ =>
          Aratio n *
            freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n)
        atTop
        (nhds
          (Aratio n *
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n)) := by
    simpa using
      (tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos n).const_mul
        (Aratio n)
  exact ge_of_tendsto hlim (hcompare_n v hv)


theorem
    freeQ2BoundaryVertexPolynomialComparisonToXAxis_of_finiteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨C, k, hC, hcompareHi⟩
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [hcompareHi] with n hcompare_n
  intro v hv
  have hlim :
      Tendsto
        (fun M : ℕ =>
          C * (n : ℝ) ^ k *
            freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n)
        atTop
        (nhds
          (C * (n : ℝ) ^ k *
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n)) := by
    simpa using
      (tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos n).const_mul
        (C * (n : ℝ) ^ k)
  exact ge_of_tendsto hlim (hcompare_n v hv)


theorem
    freeQ2BoundaryVertexPointwise_of_subexpComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass _hmass hconn
  rcases hcompare β hβpos hβc with ⟨Aratio, hAratio, hcompareHi⟩
  have hAfkHi : PositiveSubexponentialPrefactor AfkHi :=
    ⟨hconn.2.1, hconn.2.2.2.1⟩
  refine
    ⟨fun n => Aratio n * AfkHi n,
      PositiveSubexponentialPrefactor.mul hAratio hAfkHi, ?_⟩
  filter_upwards [hcompareHi, hAratio.1, hconn.2.2.2.2.2]
    with n hcompare_n hAratio_pos hfkUpper_n
  intro v hv
  calc
    ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        ≤ Aratio n *
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n :=
      hcompare_n v hv
    _ ≤ Aratio n *
        (AfkHi n * Real.exp (-(mass * (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hfkUpper_n (le_of_lt hAratio_pos)
    _ = (Aratio n * AfkHi n) *
        Real.exp (-(mass * (n : ℝ))) := by
      ring


theorem
    freeQ2BoundaryVertexPointwise_of_polynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :=
  freeQ2BoundaryVertexPointwise_of_subexpComparisonToXAxis
    (freeQ2BoundaryVertexSubexpComparisonToXAxis_of_polynomialComparison
      hcompare)


theorem
    freeQ2BoundaryVertexPointwise_of_finiteVolumeComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :=
  freeQ2BoundaryVertexPointwise_of_subexpComparisonToXAxis
    (freeQ2BoundaryVertexSubexpComparisonToXAxis_of_finiteVolumeComparison
      hcompare)


theorem
    freeQ2BoundaryVertexPointwise_of_finiteVolumePolynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :=
  freeQ2BoundaryVertexPointwise_of_polynomialComparisonToXAxis
    (freeQ2BoundaryVertexPolynomialComparisonToXAxis_of_finiteVolumePolynomial
      hcompare)


end Exact3D
end StatMech
