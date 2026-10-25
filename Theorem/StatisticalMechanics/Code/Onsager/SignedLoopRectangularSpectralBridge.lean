/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem ons_rectDual_dartVector_eq_kwRectilinearVector {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualComplexPoint dart.snd - ons_rectDualComplexPoint dart.fst =
      kwRectilinearVector (ons_rectDualDartDirection4 dart) := by
  unfold ons_rectDualComplexPoint
  rw [ons_rectDualIntPoint_snd_eq_add_step,
    triangularIntPoint_add_sub]
  by_cases hxneg : dart.snd.1.val < dart.fst.1.val
  · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
      triangularIntStep, triangularIntPoint]
  · by_cases hxpos : dart.fst.1.val < dart.snd.1.val
    · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
        hxpos, triangularIntStep, triangularIntPoint]
    · by_cases hyneg : dart.snd.2.val < dart.fst.2.val
      · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
          hxpos, hyneg, triangularIntStep, triangularIntPoint,
          kwRectilinearVector, StatMech.Onsager.BaseCase.stepOf]
      · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
          hxpos, hyneg, triangularIntStep, triangularIntPoint,
          kwRectilinearVector, StatMech.Onsager.BaseCase.stepOf]


theorem ons_rectDualDartDirection4_ne_opposite {M N : Nat}
    (dart next : (ons_rectDualGraph M N).Dart)
    (hadj : (ons_rectDualGraph M N).DartAdj dart next)
    (hedge : dart.edge ≠ next.edge) :
    ons_rectDualDartDirection4 next ≠ ons_rectDualDartDirection4 dart + 2 := by
  intro hdir
  have hvec := ons_rectDual_dartVector_eq_kwRectilinearVector dart
  have hvec' := ons_rectDual_dartVector_eq_kwRectilinearVector next
  rw [hdir] at hvec'
  have hopposite :
      kwRectilinearVector (ons_rectDualDartDirection4 dart + 2) =
        -kwRectilinearVector (ons_rectDualDartDirection4 dart) := by
    generalize ons_rectDualDartDirection4 dart = direction
    fin_cases direction <;> simp
  rw [hopposite] at hvec'
  have hsnd : dart.snd = next.fst := hadj
  have hend : next.snd = dart.fst := by
    apply ons_rectDualComplexPoint_injective
    rw [← sub_eq_zero]
    calc
      ons_rectDualComplexPoint next.snd - ons_rectDualComplexPoint dart.fst =
          (ons_rectDualComplexPoint next.snd -
              ons_rectDualComplexPoint next.fst) +
            (ons_rectDualComplexPoint dart.snd -
              ons_rectDualComplexPoint dart.fst) := by rw [← hsnd]; ring
      _ = 0 := by rw [hvec', hvec]; ring
  apply hedge
  change s(dart.fst, dart.snd) = s(next.fst, next.snd)
  rw [Sym2.eq_iff]
  exact Or.inr ⟨hend.symm, hsnd⟩

theorem ons_rectDualDartDirection4_symm {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualDartDirection4 dart.symm =
      ons_rectDualDartDirection4 dart + 2 := by
  by_cases hleft : dart.snd.1.val < dart.fst.1.val
  · have hnotright : ¬dart.fst.1.val < dart.snd.1.val :=
      not_lt_of_ge hleft.le
    simp [ons_rectDualDartDirection4, hleft, hnotright]
  · by_cases hright : dart.fst.1.val < dart.snd.1.val
    · have hnotleft : ¬dart.snd.1.val < dart.fst.1.val :=
        not_lt_of_ge hright.le
      simp [ons_rectDualDartDirection4, hright, hnotleft]
    · have hx : dart.fst.1.val = dart.snd.1.val :=
        Nat.le_antisymm (Nat.le_of_not_gt hleft) (Nat.le_of_not_gt hright)
      have hyne : dart.fst.2.val ≠ dart.snd.2.val := by
        intro hy
        apply dart.fst_ne_snd
        apply Prod.ext <;> apply Fin.ext
        · exact hx
        · exact hy
      by_cases hdown : dart.snd.2.val < dart.fst.2.val
      · have hnotup : ¬dart.fst.2.val < dart.snd.2.val :=
          not_lt_of_ge hdown.le
        simp [ons_rectDualDartDirection4, hleft, hright, hdown, hnotup]
      · have hup : dart.fst.2.val < dart.snd.2.val :=
          lt_of_le_of_ne (Nat.le_of_not_gt hdown) hyne
        simp [ons_rectDualDartDirection4, hleft, hright, hdown, hup]


theorem ons_rectDual_turnPhase_eq_turnW {M N : Nat}
    (dart next : (ons_rectDualGraph M N).Dart)
    (hadj : (ons_rectDualGraph M N).DartAdj dart next)
    (hedge : dart.edge ≠ next.edge) :
    (ons_rectDualStraightLineEmbedding M N).turnPhase dart next =
      ons_turnW ons_turnRoot (ons_rectDualDartDirection4 dart)
        (ons_rectDualDartDirection4 next) := by
  rw [← (ons_rectDualStraightLineEmbedding M N).vectorTurnPhase_eq_turnPhase]
  change kwVectorTurnPhase
      (ons_rectDualComplexPoint dart.snd - ons_rectDualComplexPoint dart.fst)
      (ons_rectDualComplexPoint next.snd - ons_rectDualComplexPoint next.fst) = _
  rw [ons_rectDual_dartVector_eq_kwRectilinearVector,
    ons_rectDual_dartVector_eq_kwRectilinearVector]
  exact kwVectorTurnPhase_rectilinear _ _
    (ons_rectDualDartDirection4_ne_opposite dart next hadj hedge)


end
end StatMech.Onsager
