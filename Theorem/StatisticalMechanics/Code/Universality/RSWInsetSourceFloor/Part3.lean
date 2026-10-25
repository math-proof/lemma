/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part3
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_affineFlipYConfig_apply (k : Int)
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rlc_affineFlipYConfig k omega e = omega (e.map (rlc_affineFlipY k)) := by
  rw [rlc_affineFlipYConfig, Equiv.piCongrLeft_apply, eq_rec_constant,
    rlc_affineFlipYEdge_symm_apply]

theorem rlc_affineFlipYConfig_involutive (k : Int)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_affineFlipYConfig k (rlc_affineFlipYConfig k omega) = omega := by
  funext e
  rw [rlc_affineFlipYConfig_apply, rlc_affineFlipYConfig_apply]
  induction e using Sym2.inductionOn with
  | _ x y => simp

theorem rlc_affineFlipYConfig_measurable (k : Int) :
    Measurable (rlc_affineFlipYConfig k) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool)
    (rlc_affineFlipYEdge k)).measurable

theorem rlc_affineFlipY_measurePreserving (k : Int) (p : NNReal) (hp : p <= 1) :
    MeasurePreserving (rlc_affineFlipYConfig k)
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) := by
  refine ⟨rlc_affineFlipYConfig_measurable k, ?_⟩
  rw [rlc_affineFlipYConfig]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure p hp)
    (rlc_affineFlipYEdge k)

theorem rlc_mem_rect_affineFlipY (a b c d k : Int) (hcd : c + d = k)
    (x : Site 2) :
    x ∈ rect a b c d ↔ rlc_affineFlipY k x ∈ rect a b c d := by
  simp only [mem_rect, rlc_affineFlipY_zero, rlc_affineFlipY_one]
  omega

theorem rlc_mem_leftSide_affineFlipY (a b c d k : Int) (hcd : c + d = k)
    (x : Site 2) :
    x ∈ leftSide a b c d ↔ rlc_affineFlipY k x ∈ leftSide a b c d := by
  rw [mem_leftSide, mem_leftSide]
  exact and_congr (rlc_mem_rect_affineFlipY a b c d k hcd x) (by simp)

theorem rlc_mem_rightSide_affineFlipY (a b c d k : Int) (hcd : c + d = k)
    (x : Site 2) :
    x ∈ rightSide a b c d ↔ rlc_affineFlipY k x ∈ rightSide a b c d := by
  rw [mem_rightSide, mem_rightSide]
  exact and_congr (rlc_mem_rect_affineFlipY a b c d k hcd x) (by simp)

theorem rlc_isOpenEdge_affineFlipY (k : Int)
    (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    IsOpenEdge 2 (rlc_affineFlipYConfig k omega) x y ↔
      IsOpenEdge 2 omega (rlc_affineFlipY k x) (rlc_affineFlipY k y) := by
  unfold IsOpenEdge
  have hedge : (s(x, y) : Sym2 (Site 2)).map (rlc_affineFlipY k) =
      s(rlc_affineFlipY k x, rlc_affineFlipY k y) := Sym2.map_mk _ _ _
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨(rlc_adj_affineFlipY k x y).mp hadj, ?_⟩
    rwa [rlc_affineFlipYConfig_apply, hedge] at hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨(rlc_adj_affineFlipY k x y).mpr hadj, ?_⟩
    rwa [rlc_affineFlipYConfig_apply, hedge]

end
end StatMech.Universality
