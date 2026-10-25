/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MultibondReindex
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetReflection.Part2
open Finset


namespace StatMech.FrontierA

noncomputable section

theorem cubicalPlaquetteZReflectEquiv_map_xySheet
    {a b c : Nat} (k : Fin (c + 1)) :
    (cubicalXYSheet (a := a) (b := b) k).map
        (cubicalPlaquetteZReflectEquiv a b c).toEmbedding =
      cubicalXYSheet (a := a) (b := b) k.rev := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [cubicalXYSheet, Finset.mem_image] at hq ⊢
    obtain ⟨ij, _, rfl⟩ := hq
    exact ⟨ij, Finset.mem_univ _, rfl⟩
  · intro hp
    simp only [cubicalXYSheet, Finset.mem_image] at hp
    obtain ⟨ij, _, rfl⟩ := hp
    rw [Finset.mem_map]
    refine ⟨CubicalPlaquette.xy ij.1 ij.2 k, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
    · simp [cubicalPlaquetteZReflectEquiv, cubicalPlaquetteZReflect]

theorem cubicalDualEnds_zReflect_agrees
    {a b c : Nat} (p : CubicalPlaquette a b c)
    (s : CubicalDualVertex a b c -> Bool) :
    (multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s)
          (cubicalDualEnds
            ((cubicalPlaquetteZReflectEquiv a b c) p)).1 =
        (multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s)
          (cubicalDualEnds
            ((cubicalPlaquetteZReflectEquiv a b c) p)).2 <->
      s (cubicalDualEnds p).1 = s (cubicalDualEnds p).2 := by
  cases p with
  | xy i j k =>
      change multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
            ((finBackward k.rev).map fun z =>
              (⟨i, j, z⟩ : CubicalCell a b c)) =
          multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
            ((finForward k.rev).map fun z =>
              (⟨i, j, z⟩ : CubicalCell a b c)) <->
        s ((finBackward k).map fun z =>
            (⟨i, j, z⟩ : CubicalCell a b c)) =
          s ((finForward k).map fun z =>
            (⟨i, j, z⟩ : CubicalCell a b c))
      rw [multibondConfigReindex_cubicalDualVertexZReflect_optionMap,
        multibondConfigReindex_cubicalDualVertexZReflect_optionMap]
      have hb : (finBackward k.rev).map (fun z =>
            (⟨i, j, z.rev⟩ : CubicalCell a b c)) =
          (finForward k).map (fun z => ⟨i, j, z⟩) := by
        change Option.map ((fun z => (⟨i, j, z⟩ : CubicalCell a b c)) ∘ Fin.rev)
            (finBackward k.rev) = _
        rw [← Option.map_map, finBackward_rev_map_rev]
      have hf : (finForward k.rev).map (fun z =>
            (⟨i, j, z.rev⟩ : CubicalCell a b c)) =
          (finBackward k).map (fun z => ⟨i, j, z⟩) := by
        change Option.map ((fun z => (⟨i, j, z⟩ : CubicalCell a b c)) ∘ Fin.rev)
            (finForward k.rev) = _
        rw [← Option.map_map, finForward_rev_map_rev]
      rw [hb, hf]
      exact eq_comm
  | xz i j k =>
      cases hb : finBackward j <;> cases hf : finForward j <;>
        simp [cubicalPlaquetteZReflectEquiv, cubicalPlaquetteZReflect,
          cubicalDualEnds, hb, hf]
  | yz i j k =>
      cases hb : finBackward i <;> cases hf : finForward i <;>
        simp [cubicalPlaquetteZReflectEquiv, cubicalPlaquetteZReflect,
          cubicalDualEnds, hb, hf]


theorem multibondDisorderFreeEnergy_cubicalXYSheet_rev
    {a b c : Nat} (beta : Real) (k : Fin (c + 1)) :
    multibondDisorderFreeEnergy
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (fun _ : CubicalPlaquette a b c => beta)
        (cubicalXYSheet k.rev) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette a b c => beta) (cubicalXYSheet k) := by
  rw [← cubicalPlaquetteZReflectEquiv_map_xySheet k]
  apply multibondDisorderFreeEnergy_reindex
    (cubicalPlaquetteZReflectEquiv a b c)
    (cubicalDualVertexZReflectEquiv a b c)
  · intro p
    rfl
  · exact cubicalDualEnds_zReflect_agrees

end
end StatMech.FrontierA
