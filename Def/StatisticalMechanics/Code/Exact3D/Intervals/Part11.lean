/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Intervals.Part9


namespace StatMech

namespace Exact3D

namespace RatInterval

def matrixVectorMul {m n : ℕ} (I : IntervalMatrix m n)
    (X : IntervalVector n) : IntervalVector m :=
  fun i => finsetSum Finset.univ fun j => mul (I i j) (X j)


def matrixVectorMulNonneg {m n : ℕ} (I : IntervalMatrix m n)
    (X : IntervalVector n) (hI : MatrixNonnegative I)
    (hX : VectorNonnegative X) : IntervalVector m :=
  fun i => finsetSum Finset.univ fun j =>
    mulNonneg (I i j) (X j) (hI i j) (hX j)


def matrixVectorResidual {n : ℕ} (I : IntervalMatrix n n)
    (X : IntervalVector n) : IntervalVector n :=
  vectorSub (matrixVectorMul I X) X


def matrixVectorResidualNonneg {n : ℕ} (I : IntervalMatrix n n)
    (X : IntervalVector n) (hI : MatrixNonnegative I)
    (hX : VectorNonnegative X) : IntervalVector n :=
  vectorSub (matrixVectorMulNonneg I X hI hX) X


def matrixVectorAffine {m n : ℕ} (I : IntervalMatrix m n)
    (B : IntervalVector m) (X : IntervalVector n) : IntervalVector m :=
  vectorAdd (matrixVectorMul I X) B


def matrixVectorAffineNonneg {m n : ℕ} (I : IntervalMatrix m n)
    (B : IntervalVector m) (X : IntervalVector n)
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X) :
    IntervalVector m :=
  vectorAdd (matrixVectorMulNonneg I X hI hX) B


def matrixVectorAffineResidual {n : ℕ} (I : IntervalMatrix n n)
    (B : IntervalVector n) (X : IntervalVector n) : IntervalVector n :=
  vectorSub (matrixVectorAffine I B X) X


def matrixVectorAffineResidualNonneg {n : ℕ} (I : IntervalMatrix n n)
    (B : IntervalVector n) (X : IntervalVector n)
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X) :
    IntervalVector n :=
  vectorSub (matrixVectorAffineNonneg I B X hI hX) X


end RatInterval
end Exact3D
end StatMech
