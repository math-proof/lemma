/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part4


namespace StatMech

namespace Exact3D

namespace RatInterval

def GershgorinRowExcludes {n : ℕ}
    (A : Fin n → Fin n → ℝ) (lam : ℝ) (i : Fin n) : Prop :=
  offDiagAbsRowSum A i < |lam - A i i|


def IntervalGershgorinRowExcludes {n : ℕ}
    (I : IntervalMatrix n n) (lam : ℝ) (i : Fin n) : Prop :=
  ∀ a : ℝ, (I i i).MemR a →
    (IntervalOffDiagAbsRowSum I i : ℝ) < |lam - a|


def IntervalGershgorinRowEndpointSeparated {n : ℕ}
    (I : IntervalMatrix n n) (lam : ℝ) (i : Fin n) : Prop :=
  lam + (IntervalOffDiagAbsRowSum I i : ℝ) < ((I i i).lower : ℝ) ∨
    ((I i i).upper : ℝ) + (IntervalOffDiagAbsRowSum I i : ℝ) < lam


def IntervalGershgorinRowEndpointSeparatedOnIcc {n : ℕ}
    (I : IntervalMatrix n n) (lo hi : ℝ) (i : Fin n) : Prop :=
  hi + (IntervalOffDiagAbsRowSum I i : ℝ) < ((I i i).lower : ℝ) ∨
    ((I i i).upper : ℝ) + (IntervalOffDiagAbsRowSum I i : ℝ) < lo


end RatInterval
end Exact3D
end StatMech
