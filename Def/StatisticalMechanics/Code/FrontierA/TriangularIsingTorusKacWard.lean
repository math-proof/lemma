/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2


namespace StatMech.FrontierA

open scoped Matrix


noncomputable def triangularKacWardTurnMatrix
    (rho : Complex) : Matrix (Fin 6) (Fin 6) Complex :=
  !![1, 0, rho ^ 2, -(rho ^ 6), rho, -(rho ^ 5);
     0, 1, -(rho ^ 6), rho ^ 2, -(rho ^ 5), rho;
     -(rho ^ 6), rho ^ 2, 1, 0, -(rho ^ 7), rho ^ 3;
     rho ^ 2, -(rho ^ 6), 0, 1, rho ^ 3, -(rho ^ 7);
     -(rho ^ 7), rho ^ 3, rho, -(rho ^ 5), 1, 0;
     rho ^ 3, -(rho ^ 7), -(rho ^ 5), rho, 0, 1]


noncomputable def triangularKacWardWeightDiagonal
    (t1 t2 t3 z1 z2 z3 : Complex) : Matrix (Fin 6) (Fin 6) Complex :=
  Matrix.diagonal ![t1 * z1, t1 * z1⁻¹, t2 * z2,
    t2 * z2⁻¹, t3 * z3, t3 * z3⁻¹]


noncomputable def triangularKacWardSymbolMatrix
    (t1 t2 t3 rho z1 z2 z3 : Complex) :
    Matrix (Fin 6) (Fin 6) Complex :=
  1 - triangularKacWardWeightDiagonal t1 t2 t3 z1 z2 z3 *
    triangularKacWardTurnMatrix rho

noncomputable def triangularKacWardDiagonalSymbol
    (d0 d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 6) (Fin 6) Complex :=
  1 - Matrix.diagonal ![d0, d1, d2, d3, d4, d5] *
    triangularKacWardTurnMatrix rho

noncomputable def triangularKacWardMinor0
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![1 - d1, d1 * rho ^ 6, -(d1 * rho ^ 2), d1 * rho ^ 5, -(d1 * rho);
     -(d2 * rho ^ 2), 1 - d2, 0, d2 * rho ^ 7, -(d2 * rho ^ 3);
     d3 * rho ^ 6, 0, 1 - d3, -(d3 * rho ^ 3), d3 * rho ^ 7;
     -(d4 * rho ^ 3), -(d4 * rho), d4 * rho ^ 5, 1 - d4, 0;
     d5 * rho ^ 7, d5 * rho ^ 5, -(d5 * rho), 0, 1 - d5]

noncomputable def triangularKacWardMinor1
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, d1 * rho ^ 6, -(d1 * rho ^ 2), d1 * rho ^ 5, -(d1 * rho);
     d2 * rho ^ 6, 1 - d2, 0, d2 * rho ^ 7, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), 0, 1 - d3, -(d3 * rho ^ 3), d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho), d4 * rho ^ 5, 1 - d4, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 5, -(d5 * rho), 0, 1 - d5]

noncomputable def triangularKacWardMinor2
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, -(d1 * rho ^ 2), d1 * rho ^ 5, -(d1 * rho);
     d2 * rho ^ 6, -(d2 * rho ^ 2), 0, d2 * rho ^ 7, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), d3 * rho ^ 6, 1 - d3, -(d3 * rho ^ 3), d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho ^ 3), d4 * rho ^ 5, 1 - d4, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 7, -(d5 * rho), 0, 1 - d5]

noncomputable def triangularKacWardMinor3
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, d1 * rho ^ 6, d1 * rho ^ 5, -(d1 * rho);
     d2 * rho ^ 6, -(d2 * rho ^ 2), 1 - d2, d2 * rho ^ 7, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), d3 * rho ^ 6, 0, -(d3 * rho ^ 3), d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho ^ 3), -(d4 * rho), 1 - d4, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 7, d5 * rho ^ 5, 0, 1 - d5]

noncomputable def triangularKacWardMinor4
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, d1 * rho ^ 6, -(d1 * rho ^ 2), -(d1 * rho);
     d2 * rho ^ 6, -(d2 * rho ^ 2), 1 - d2, 0, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), d3 * rho ^ 6, 0, 1 - d3, d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho ^ 3), -(d4 * rho), d4 * rho ^ 5, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 7, d5 * rho ^ 5, -(d5 * rho), 1 - d5]

noncomputable def triangularKacWardMinor5
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, d1 * rho ^ 6, -(d1 * rho ^ 2), d1 * rho ^ 5;
     d2 * rho ^ 6, -(d2 * rho ^ 2), 1 - d2, 0, d2 * rho ^ 7;
     -(d3 * rho ^ 2), d3 * rho ^ 6, 0, 1 - d3, -(d3 * rho ^ 3);
     d4 * rho ^ 7, -(d4 * rho ^ 3), -(d4 * rho), d4 * rho ^ 5, 1 - d4;
     -(d5 * rho ^ 3), d5 * rho ^ 7, d5 * rho ^ 5, -(d5 * rho), 0]

end StatMech.FrontierA
