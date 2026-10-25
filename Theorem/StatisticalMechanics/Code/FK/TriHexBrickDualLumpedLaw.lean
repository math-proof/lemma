/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualBundles
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part3
import Def.StatisticalMechanics.Code.FK.TriHexBrickDualLumpedLaw
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

theorem triHexBrickDualLumpedParam_compatible
    (N m : Nat) (p : Real) :
    ocd_ParamCompatible (triHexBrickInnerFaceMap N m)
      (fun _ => p) (triHexBrickDualLumpedParam N m p) := by
  intro e
  simp [triHexBrickDualLumpedParam]


theorem triHexBrickDualLumpedParam_eq_effective_on_edge
    {N m : Nat} (hNm : N < m) (p : Real)
    {a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))}
    (ha : a ∈ (triHexBrickFullDualGraph m).edgeSet) :
    triHexBrickDualLumpedParam N m p a =
      indexedEffectiveParam
        (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a := by
  unfold triHexBrickDualLumpedParam
  split
  · rename_i hrange
    obtain ⟨e, rfl⟩ := hrange
    have himage : ocd_innerEdge (triHexBrickInnerFaceMap N m) e ∈
        (triHexBrickInnerTriangleGraph N).edgeFinset.image
          (ocd_innerEdge (triHexBrickInnerFaceMap N m)) := by
      rw [ocd_innerEdge_image_edgeFinset
        (triHexBrickInnerFaceMap_injective hNm)
        (triHexBrickInnerFaceMap_adjMatch hNm)]
      exact Finset.mem_filter.mpr
        ⟨by simpa only [SimpleGraph.mem_edgeFinset] using ha, ⟨e, rfl⟩⟩
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp himage
    have heq : e = b :=
      ocd_innerEdge_injective _
        (triHexBrickInnerFaceMap_injective hNm) hbe.symm
    subst e
    change p = pfdEffectiveParam (triHexPlanarFiniteStarPlanar m) p
      (ocd_innerEdge (triHexBrickInnerFaceMap N m) b)
    exact (triHexBrick_pfdEffectiveParam_innerEdge
      hNm p ⟨b, hb⟩).symm
  · simp [ha]

theorem triHexBrickDualLumpedParam_pos
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))) :
    0 < triHexBrickDualLumpedParam N m p a := by
  unfold triHexBrickDualLumpedParam
  split
  · exact hp
  · split
    · rename_i ha
      change 0 < pfdEffectiveParam
        (triHexPlanarFiniteStarPlanar m) p a
      exact pfdEffectiveParam_pos _ hp hp1 ha
    · norm_num

theorem triHexBrickDualLumpedParam_lt_one
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))) :
    triHexBrickDualLumpedParam N m p a < 1 := by
  unfold triHexBrickDualLumpedParam
  split
  · exact hp1
  · split
    · change pfdEffectiveParam
        (triHexPlanarFiniteStarPlanar m) p a < 1
      exact pfdEffectiveParam_lt_one _ hp hp1 _
    · norm_num

theorem triHexBrick_edgeProductW_lumpedParam_extendActive
    {N m : Nat} (hNm : N < m) (p : Real)
    (rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet) :
    edgeProductW (triHexBrickFullDualGraph m)
        (triHexBrickDualLumpedParam N m p)
        (extendActive (triHexBrickFullDualGraph m) rho) =
      ∏ a : (triHexBrickFullDualGraph m).edgeSet,
        if rho a then
          indexedEffectiveParam
            (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a.1
        else 1 - indexedEffectiveParam
          (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a.1 := by
  unfold edgeProductW
  rw [← Finset.prod_attach (triHexBrickFullDualGraph m).edgeFinset,
    Finset.attach_eq_univ]
  let edgeEquiv : (triHexBrickFullDualGraph m).edgeFinset ≃
      (triHexBrickFullDualGraph m).edgeSet :=
    { toFun := fun e =>
        ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      invFun := fun e =>
        ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  apply Fintype.prod_equiv edgeEquiv
  intro e
  change (if extendActive (triHexBrickFullDualGraph m) rho
        (edgeEquiv e).1 then
      triHexBrickDualLumpedParam N m p (edgeEquiv e).1
    else 1 - triHexBrickDualLumpedParam N m p (edgeEquiv e).1) = _
  rw [extendActive_apply,
    triHexBrickDualLumpedParam_eq_effective_on_edge
      hNm _ (edgeEquiv e).2]


theorem triHexBrick_pfdIndexedWeight_lumping
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real) :
    (∑ eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (pfdIndexedSupportActive
          (triHexPlanarFiniteStarPlanar m) eta) *
          q ^ numClustersBC (triHexBrickFullDualGraph m) ⊥
            (extendActive (triHexBrickFullDualGraph m)
              (pfdIndexedSupportActive
                (triHexPlanarFiniteStarPlanar m) eta)))) =
    ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
      F rho * activeBCWeight (triHexBrickFullDualGraph m) ⊥
        (triHexBrickDualLumpedParam N m p) q rho := by
  have h := sum_indexedBernoulliWeight_restrictActive_bundleSupport
    (triHexBrickFullDualGraph m) p
    (kwg_dualEnds (triHexPlanarFiniteStarPlanar m))
    (fun rho => F rho * q ^ numClustersBC
      (triHexBrickFullDualGraph m) ⊥
        (extendActive (triHexBrickFullDualGraph m) rho))
  change (∑ eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (restrictActive (triHexBrickFullDualGraph m)
          (indexedBundleSupport
            (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) eta)) *
        q ^ numClustersBC (triHexBrickFullDualGraph m) ⊥
          (extendActive (triHexBrickFullDualGraph m)
            (restrictActive (triHexBrickFullDualGraph m)
              (indexedBundleSupport
                (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) eta))))) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro rho _
  rw [activeBCWeight,
    triHexBrick_edgeProductW_lumpedParam_extendActive hNm]
  ring


end
end StatMech.FK.PeriodicPlanar
