/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPropIV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPropIV


namespace StatMech.Onsager

open BigOperators


def ons_SelfAvoiding {L n : ℕ} (site : Fin (n + 1) → ZMod L × ZMod L) : Prop :=
  Function.Injective (fun k : Fin n => site k.castSucc)


def ons_DiscreteUmlaufsatzKW : Prop :=
  ∀ (L n : ℕ) (d : Fin (n + 1) → Fin 4) (site : Fin (n + 1) → ZMod L × ZMod L),
    (∀ k : Fin n, site k.succ = ons_dirStep L (d k.castSucc) (site k.castSucc)) →
    (∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) →
    d (Fin.last n) = d 0 → site (Fin.last n) = site 0 →
    ons_SelfAvoiding site →
    ∀ m : ℤ, (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m → Odd m


end StatMech.Onsager
