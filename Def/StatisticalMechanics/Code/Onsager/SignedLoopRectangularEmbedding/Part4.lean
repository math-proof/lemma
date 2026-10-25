/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part3
open Set SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

def ons_rectDualStraightLineEmbedding (M N : Nat) :
    KWStraightLineEmbedding (ons_rectDualGraph M N) where
  vertex := ons_rectDualComplexPoint
  vertex_injective := ons_rectDualComplexPoint_injective
  vertex_not_strictly_between := by
    intro dart v hvfst hvsnd hbetween
    let a := ons_rectDualDartDirection dart
    have ha : ons_rectDualIntPoint dart.snd =
        ons_rectDualIntPoint dart.fst + triangularIntStep a :=
      ons_rectDualIntPoint_snd_eq_add_step dart
    apply triangularIntPoint_not_strictly_between_step
      (ons_rectDualIntPoint dart.fst) (ons_rectDualIntPoint v) a
    · intro h
      exact hvfst (ons_rectDualIntPoint_injective h)
    · intro h
      apply hvsnd
      apply ons_rectDualIntPoint_injective
      exact h.trans ha.symm
    · simpa only [ons_rectDualComplexPoint, ← ha] using hbetween
  edgeInteriors_disjoint := by
    intro dart next hedge
    rw [Set.disjoint_left]
    intro z hz hz'
    have hzStep : Sbtw Real
        (triangularIntPoint (ons_rectDualIntPoint dart.fst)) z
        (triangularIntPoint (ons_rectDualIntPoint dart.fst +
          triangularIntStep (ons_rectDualDartDirection dart))) := by
      rw [← ons_rectDualIntPoint_snd_eq_add_step]
      exact hz
    have hzStep' : Sbtw Real
        (triangularIntPoint (ons_rectDualIntPoint next.fst)) z
        (triangularIntPoint (ons_rectDualIntPoint next.fst +
          triangularIntStep (ons_rectDualDartDirection next))) := by
      rw [← ons_rectDualIntPoint_snd_eq_add_step]
      exact hz'
    have hedgeInt := triangular_open_intersection_edge_eq
      (ons_rectDualIntPoint dart.fst) (ons_rectDualIntPoint next.fst)
      (ons_rectDualDartDirection dart) (ons_rectDualDartDirection next)
      z hzStep hzStep'
    rw [← ons_rectDualIntPoint_snd_eq_add_step,
      ← ons_rectDualIntPoint_snd_eq_add_step, Sym2.eq_iff] at hedgeInt
    apply hedge
    change s(dart.fst, dart.snd) = s(next.fst, next.snd)
    rw [Sym2.eq_iff]
    rcases hedgeInt with h | h
    · exact Or.inl ⟨ons_rectDualIntPoint_injective h.1,
        ons_rectDualIntPoint_injective h.2⟩
    · exact Or.inr ⟨ons_rectDualIntPoint_injective h.1,
        ons_rectDualIntPoint_injective h.2⟩


def ons_rectDualPathCanonicalDefectKWDet {M N : Nat}
    (path : ons_RectDualPath M N) (x : Real) : Complex :=
  ons_rectDualPathDefectKWDet (ons_rectDualStraightLineEmbedding M N) path x


def ons_rectDualCanonicalKWDet (M N : Nat) (x : Real) : Complex :=
  ons_rectDualKWDet (ons_rectDualStraightLineEmbedding M N) x

end
end StatMech.Onsager
