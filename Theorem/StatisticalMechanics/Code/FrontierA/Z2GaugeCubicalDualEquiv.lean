/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

theorem cubicalLowerXYTrace_injective {a b c : Nat}
    (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (fun A : ClosedCubicalSurface a b c =>
      cubicalLowerXYTrace A.1) := by
  intro A B htrace
  have hA : IsClosedPlaquetteSet cubicalPlaquetteIncidence A.1 :=
    (mem_gaugeClosedSurfaceFamily_iff cubicalPlaquetteIncidence A.1).mp A.2
  have hB : IsClosedPlaquetteSet cubicalPlaquetteIncidence B.1 :=
    (mem_gaugeClosedSurfaceFamily_iff cubicalPlaquetteIncidence B.1).mp B.2
  have hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence (A.1 ∆ B.1) := by
    intro e
    apply (even_plaquetteIncidenceCount_symmDiff_iff
      cubicalPlaquetteIncidence A.1 B.1 e).mpr
    exact ⟨fun _ => hB e, fun _ => hA e⟩
  have hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ A.1 ∆ B.1 := by
    intro i j k
    have hmem := Finset.ext_iff.mp htrace ⟨i, j, k⟩
    simp only [cubicalLowerXYTrace, mem_filter, mem_univ, true_and] at hmem
    simp [mem_symmDiff, hmem]
  have hempty := closed_eq_empty_of_lowerXY_not_mem hb hc
    (A.1 ∆ B.1) hclosed hxy
  apply Subtype.ext
  exact Finset.symmDiff_eq_empty.mp hempty

end
end StatMech.FrontierA
