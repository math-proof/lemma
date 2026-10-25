/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


@[simp] theorem pairSiteLeft_pair (eta zeta : ConfigSpace (Site d)) :
    pairSiteLeft (pairSiteConfig eta zeta) = eta := rfl

@[simp] theorem pairSiteRight_pair (eta zeta : ConfigSpace (Site d)) :
    pairSiteRight (pairSiteConfig eta zeta) = zeta := rfl


theorem measurable_pairSiteConfig : Measurable
    (Function.uncurry pairSiteConfig :
      (ConfigSpace (Site d) × ConfigSpace (Site d)) → PairSiteConfig d) := by
  rw [measurable_pi_iff]
  intro e
  cases e with
  | inl x => exact (measurable_pi_apply x).comp measurable_fst
  | inr x => exact (measurable_pi_apply x).comp measurable_snd

theorem measurable_pairSiteLeft :
    Measurable (pairSiteLeft : PairSiteConfig d → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  exact fun x => measurable_pi_apply (Sum.inl x)

theorem measurable_pairSiteRight :
    Measurable (pairSiteRight : PairSiteConfig d → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  exact fun x => measurable_pi_apply (Sum.inr x)


theorem pairSiteConfig_shift (g : Multiplicative (Site d))
    (eta zeta : ConfigSpace (Site d)) :
    pairSiteConfig (shift g eta) (shift g zeta) =
      shift g (pairSiteConfig eta zeta) := by
  funext e
  cases e <;> rfl


end StatMech.FrontierA
