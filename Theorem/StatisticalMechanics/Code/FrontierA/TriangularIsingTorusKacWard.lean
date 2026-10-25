/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusKacWard


namespace StatMech.FrontierA

open scoped Matrix


theorem triangularKacWardDiagonalSymbol_submatrix0
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (0 : Fin 6).succAbove =
        triangularKacWardMinor0 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor0, Fin.succAbove]

theorem triangularKacWardDiagonalSymbol_submatrix1
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (1 : Fin 6).succAbove =
        triangularKacWardMinor1 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor1, Fin.succAbove]

theorem triangularKacWardDiagonalSymbol_submatrix2
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (2 : Fin 6).succAbove =
        triangularKacWardMinor2 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor2, Fin.succAbove]

theorem triangularKacWardDiagonalSymbol_submatrix3
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (3 : Fin 6).succAbove =
        triangularKacWardMinor3 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor3, Fin.succAbove]

theorem triangularKacWardDiagonalSymbol_submatrix4
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (4 : Fin 6).succAbove =
        triangularKacWardMinor4 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor4, Fin.succAbove]

theorem triangularKacWardDiagonalSymbol_submatrix5
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (5 : Fin 6).succAbove =
        triangularKacWardMinor5 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor5, Fin.succAbove]

end StatMech.FrontierA
