/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns.Part5


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind


def ons_windingTranslation (L : ℕ) (mx my : ℤ) : ℤ × ℤ :=
  ((L : ℤ) * mx, (L : ℤ) * my)


def ons_periodicLiftVertex {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) (mx my r : ℤ) (i : Fin n) : ℤ × ℤ :=
  pos (ons_liftDir v) i +
    ((L : ℤ) * (r * mx), (L : ℤ) * (r * my))


def ons_liftBase {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) : ℤ × ℤ :=
  (((ons_liftSite v 0).1.val : ℤ),
    ((ons_liftSite v 0).2.val : ℤ))


def ons_anchoredPeriodicLiftVertex {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) (mx my r : ℤ) (i : Fin n) : ℤ × ℤ :=
  ons_liftBase v + ons_periodicLiftVertex v mx my r i


end StatMech.Onsager
