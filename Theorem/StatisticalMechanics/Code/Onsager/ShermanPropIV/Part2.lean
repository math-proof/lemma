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
import Def.StatisticalMechanics.Code.Onsager.ShermanPropIV


namespace StatMech.Onsager

open BigOperators


theorem ons_propIV_of_umlaufsatz (hU : ons_DiscreteUmlaufsatzKW)
    (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (L n : ℕ) (d : Fin (n + 1) → Fin 4) (site : Fin (n + 1) → ZMod L × ZMod L)
    (hstep : ∀ k : Fin n, site k.succ = ons_dirStep L (d k.castSucc) (site k.castSucc))
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
    (hcd : d (Fin.last n) = d 0) (hcs : site (Fin.last n) = site 0)
    (hsa : ons_SelfAvoiding site) :
    ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = -1 := by
  obtain ⟨m, hm, _⟩ := ons_closed_walk_prod ω hω hI n d hnu hcd
  have hodd : Odd m := hU L n d site hstep hnu hcd hcs hsa m hm
  exact ons_selfAvoiding_prod ω hω hI n d hnu m hm hodd

end StatMech.Onsager
