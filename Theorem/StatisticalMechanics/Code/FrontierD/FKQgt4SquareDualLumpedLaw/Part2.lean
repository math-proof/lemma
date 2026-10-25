/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles.Part2
import Theorem.StatisticalMechanics.Code.FK.IndexedEdgeLumping.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

theorem fkSquareDualLumpedParam_compatible
    (N m : Nat) (p : Real) :
    ocd_ParamCompatible (fkSquareBox_innerFaceMap N m)
      (fun _ => p) (fkSquareDualLumpedParam N m p) := by
  intro e
  simp [fkSquareDualLumpedParam]

theorem indexedEffectiveParam_eq_pfdEffectiveParam
    (P : PlanarZ2Subgraph) (p : Real)
    (a : Sym2 (kwg_Face P)) :
    indexedEffectiveParam (kwg_dualEnds P) p a =
      pfdEffectiveParam P p a := by
  rfl


theorem fkSquareDualLumpedParam_eq_effective_on_edge
    {N m : Nat} (hNm : N < m) (p : Real)
    {a : Sym2 (kwg_Face (fkSquareBoxPlanar m))}
    (ha : a ∈ (fkSquareBoxFullDualGraph m).edgeSet) :
    fkSquareDualLumpedParam N m p a =
      indexedEffectiveParam (kwg_dualEnds (fkSquareBoxPlanar m)) p a := by
  unfold fkSquareDualLumpedParam
  split
  · rename_i hrange
    obtain ⟨e, rfl⟩ := hrange
    have himage : ocd_innerEdge (fkSquareBox_innerFaceMap N m) e ∈
        (FK.boxGraph 2 N).edgeFinset.image
          (ocd_innerEdge (fkSquareBox_innerFaceMap N m)) := by
      rw [ocd_innerEdge_image_edgeFinset
        (fkSquareBox_innerFaceMap_injective hNm)
        (fkSquareBox_innerFaceMap_adjMatch hNm)]
      exact Finset.mem_filter.mpr
        ⟨by simpa only [SimpleGraph.mem_edgeFinset] using ha, ⟨e, rfl⟩⟩
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp himage
    have heq : e = b :=
      ocd_innerEdge_injective _ (fkSquareBox_innerFaceMap_injective hNm) hbe.symm
    subst e
    rw [indexedEffectiveParam_eq_pfdEffectiveParam]
    exact (pfdEffectiveParam_innerEdge hNm p ⟨b, hb⟩).symm
  · simp [ha]

theorem fkSquareDualLumpedParam_pos
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (fkSquareBoxPlanar m))) :
    0 < fkSquareDualLumpedParam N m p a := by
  unfold fkSquareDualLumpedParam
  split
  · exact hp
  · split
    · rename_i ha
      rw [indexedEffectiveParam_eq_pfdEffectiveParam]
      exact pfdEffectiveParam_pos _ hp hp1 ha
    · norm_num

theorem fkSquareDualLumpedParam_lt_one
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (fkSquareBoxPlanar m))) :
    fkSquareDualLumpedParam N m p a < 1 := by
  unfold fkSquareDualLumpedParam
  split
  · exact hp1
  · split
    · rw [indexedEffectiveParam_eq_pfdEffectiveParam]
      exact pfdEffectiveParam_lt_one _ hp hp1 _
    · norm_num

theorem edgeProductW_lumpedParam_extendActive
    {N m : Nat} (hNm : N < m) (p : Real)
    (rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet) :
    edgeProductW (fkSquareBoxFullDualGraph m)
        (fkSquareDualLumpedParam N m p)
        (extendActive (fkSquareBoxFullDualGraph m) rho) =
      ∏ a : (fkSquareBoxFullDualGraph m).edgeSet,
        if rho a then
          indexedEffectiveParam (kwg_dualEnds (fkSquareBoxPlanar m)) p a.1
        else 1 - indexedEffectiveParam
          (kwg_dualEnds (fkSquareBoxPlanar m)) p a.1 := by
  unfold edgeProductW
  rw [← Finset.prod_attach (fkSquareBoxFullDualGraph m).edgeFinset,
    Finset.attach_eq_univ]
  let edgeEquiv : (fkSquareBoxFullDualGraph m).edgeFinset ≃
      (fkSquareBoxFullDualGraph m).edgeSet :=
    { toFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      invFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  apply Fintype.prod_equiv edgeEquiv
  intro e
  change (if extendActive (fkSquareBoxFullDualGraph m) rho (edgeEquiv e).1 then
      fkSquareDualLumpedParam N m p (edgeEquiv e).1
    else 1 - fkSquareDualLumpedParam N m p (edgeEquiv e).1) = _
  rw [extendActive_apply,
    fkSquareDualLumpedParam_eq_effective_on_edge hNm _ (edgeEquiv e).2]


theorem pfdIndexedWeight_lumping
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real) :
    (∑ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta) *
          q ^ numClustersBC (fkSquareBoxFullDualGraph m) ⊥
            (extendActive (fkSquareBoxFullDualGraph m)
              (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta)))) =
    ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
      F rho * activeBCWeight (fkSquareBoxFullDualGraph m) ⊥
        (fkSquareDualLumpedParam N m p) q rho := by
  have h := sum_indexedBernoulliWeight_restrictActive_bundleSupport
    (fkSquareBoxFullDualGraph m) p
    (kwg_dualEnds (fkSquareBoxPlanar m))
    (fun rho => F rho * q ^ numClustersBC
      (fkSquareBoxFullDualGraph m) ⊥
        (extendActive (fkSquareBoxFullDualGraph m) rho))
  change (∑ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (restrictActive (fkSquareBoxFullDualGraph m)
          (indexedBundleSupport (kwg_dualEnds (fkSquareBoxPlanar m)) eta)) *
        q ^ numClustersBC (fkSquareBoxFullDualGraph m) ⊥
          (extendActive (fkSquareBoxFullDualGraph m)
            (restrictActive (fkSquareBoxFullDualGraph m)
              (indexedBundleSupport (kwg_dualEnds (fkSquareBoxPlanar m)) eta))))) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro rho _
  rw [activeBCWeight,
    edgeProductW_lumpedParam_extendActive hNm]
  ring


end
end StatMech.FrontierD
