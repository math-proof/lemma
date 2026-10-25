/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourAuditedCoordinateHorizontalRows_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateHorizontalRows := by
  rintro ⟨firstSeam, secondSeam, middle, last⟩
    ⟨firstSeam', secondSeam', middle', last'⟩ hrows
  have hfirst := congrArg Prod.fst hrows
  have hsecond := congrArg Prod.snd hrows
  let p := sixVertexFourByFourAuditedCoordinateParameters
    ⟨firstSeam, secondSeam, middle, last⟩
  let p' := sixVertexFourByFourAuditedCoordinateParameters
    ⟨firstSeam', secondSeam', middle', last'⟩
  have hfirstZero : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowZero p.1).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowZero p'.1).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (0 : Fin 4)
  have hsecondZero : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowZero p.1).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowZero p'.1).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (0 : Fin 4)
  have hzero : p.1 = p'.1 :=
    sixVertexFourByFourAuditedRowZero_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowZero_lt p.1).1
        (sixVertexFourByFourAuditedRowZero_lt p'.1).1 hfirstZero)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowZero_lt p.1).2
        (sixVertexFourByFourAuditedRowZero_lt p'.1).2 hsecondZero))
  have hseams : (firstSeam, secondSeam) = (firstSeam', secondSeam') :=
    sixVertexFourByFourAuditedCoordinateRowZero_injective hzero
  cases hseams
  have hfirstOne : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.1).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.1).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (1 : Fin 4)
  have hsecondOne : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.1).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.1).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (1 : Fin 4)
  have hone : p.2.1 = p'.2.1 :=
    sixVertexFourByFourAuditedRowMiddle_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.1).1
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.1).1 hfirstOne)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.1).2
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.1).2 hsecondOne))
  have hfirstTwo : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.2.1).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (2 : Fin 4)
  have hsecondTwo : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.2.1).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (2 : Fin 4)
  have htwo : p.2.2.1 = p'.2.2.1 :=
    sixVertexFourByFourAuditedRowMiddle_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.2.1).1
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.2.1).1 hfirstTwo)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.2.1).2
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.2.1).2 hsecondTwo))
  have hmiddlePair :
      sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam middle =
        sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam middle' :=
    Prod.ext hone htwo
  have hmiddle := sixVertexFourByFourAuditedMiddlePair_injective
    firstSeam secondSeam hmiddlePair
  subst middle'
  have hfirstThree : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowLast p.2.2.2).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowLast p'.2.2.2).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (3 : Fin 4)
  have hsecondThree : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowLast p.2.2.2).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowLast p'.2.2.2).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (3 : Fin 4)
  have hlast : p.2.2.2 = p'.2.2.2 :=
    sixVertexFourByFourAuditedRowLast_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowLast_lt p.2.2.2).1
        (sixVertexFourByFourAuditedRowLast_lt p'.2.2.2).1 hfirstThree)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowLast_lt p.2.2.2).2
        (sixVertexFourByFourAuditedRowLast_lt p'.2.2.2).2 hsecondThree))
  change last = last' at hlast
  subst last'
  rfl

theorem sixVertexFourByFourAuditedCoordinateTargetPair_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateTargetPair := by
  intro c d htarget
  apply sixVertexFourByFourAuditedCoordinateHorizontalRows_injective
  apply Prod.ext
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.1.horizontal) htarget) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateTargetPair,
      sixVertexFourByFourAuditedParamTargetFirst,
      sixVertexFourByFourToggleVerticalColumn,
      sixVertexFourByFourAuditedParamSourceFirst] using hhorizontal
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.2.horizontal) htarget) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateTargetPair,
      sixVertexFourByFourAuditedParamTargetSecond,
      sixVertexFourByFourToggleVerticalColumn,
      sixVertexFourByFourAuditedParamSourceSecond] using hhorizontal

theorem sixVertexFourByFourAuditedCoordinateSourcePair_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateSourcePair := by
  intro c d hsource
  apply sixVertexFourByFourAuditedCoordinateHorizontalRows_injective
  apply Prod.ext
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.1.horizontal) hsource) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateSourcePair,
      sixVertexFourByFourAuditedParamSourceFirst] using hhorizontal
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.2.horizontal) hsource) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateSourcePair,
      sixVertexFourByFourAuditedParamSourceSecond] using hhorizontal

theorem sixVertexFourByFourAuditedCoordinate_matching :
    Function.Injective sixVertexFourByFourAuditedCoordinateSourcePair /\
      Function.Injective sixVertexFourByFourAuditedCoordinateTargetPair /\
      forall c,
        SixVertexFourByFourAuditedCoordinateSourcePairValid c /\
          SixVertexFourByFourAuditedCoordinateTargetPairValid c /\
          sixVertexPairAtMostTwoCycleFineRelated
            (sixVertexFourByFourAuditedCoordinateSourcePair c)
            (sixVertexFourByFourAuditedCoordinateTargetPair c) := by
  constructor
  · exact sixVertexFourByFourAuditedCoordinateSourcePair_injective
  constructor
  · exact sixVertexFourByFourAuditedCoordinateTargetPair_injective
  · intro c
    constructor
    · exact sixVertexFourByFourAuditedCoordinateSourcePair_valid c
    constructor
    · exact sixVertexFourByFourAuditedCoordinateTargetPair_valid c
    · exact sixVertexFourByFourAuditedCoordinate_fineRelated c

theorem sixVertexFourByFourAuditedCoordinateParameters_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateParameters := by
  intro c d hparameters
  apply sixVertexFourByFourAuditedCoordinateHorizontalRows_injective
  simp only [sixVertexFourByFourAuditedCoordinateHorizontalRows]
  rw [hparameters]

end
end StatMech.FrontierD
