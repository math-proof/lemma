/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_translate_clusterInfinite_iff (t : Site 2)
    (omega : ConfigSpace (Sym2 (Site 2))) (x : Site 2) :
    (cluster 2 (translateConfig t omega) x).Infinite ↔
      (cluster 2 omega (x + t)).Infinite := by
  let e : Site 2 ≃ Site 2 := Equiv.addRight t
  have himage : e '' cluster 2 (translateConfig t omega) x =
      cluster 2 omega (e x) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (zfk_translateOpenIso t omega).reachable_iff.mpr hy
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      apply (zfk_translateOpenIso t omega).reachable_iff.mp
      change Connected 2 omega (x + t) (e.symm z + t)
      have he : e.symm z + t = z := e.apply_symm_apply z
      rwa [he]
  change (cluster 2 (translateConfig t omega) x).Infinite ↔
    (cluster 2 omega (e x)).Infinite
  rw [← himage]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem zfk_connectedWithin_translate_iff
    (a b c d : ℤ) (t : Site 2) (omega : ConfigSpace (Sym2 (Site 2)))
    (x y : Site 2) (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d) :
    ConnectedWithin 2 (translateConfig t omega) (rect a b c d)
        ⟨x, hx⟩ ⟨y, hy⟩ ↔
      ConnectedWithin 2 omega
        (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))
        ⟨x + t, (cti_mem_rect_translate a b c d t x).mp hx⟩
        ⟨y + t, (cti_mem_rect_translate a b c d t y).mp hy⟩ := by
  constructor
  · intro h
    exact h.map (cti_inducedHom a b c d t omega)
  · intro h
    have hm := h.map (cti_inducedHomInv a b c d t omega)
    convert hm using 1 <;> apply Subtype.ext <;> simp [cti_inducedHomInv]


end StatMech.TwoDim
