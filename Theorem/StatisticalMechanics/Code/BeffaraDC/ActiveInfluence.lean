/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.BeffaraDC.ActiveRussoHamming
import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
open scoped BigOperators


namespace StatMech.BeffaraDC

open Finset

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem activeWeight_open_pair {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    p * activeWeight G (fun _ => p) q (setClosed e ω) ≤
      q * (1 - p) * activeWeight G (fun _ => p) q (setOpen e ω) := by
  unfold activeWeight fkWeightW
  rw [extendActive_setOpen, extendActive_setClosed,
    edgeProductW_setOpen, edgeProductW_setClosed]
  let R := ∏ a ∈ G.edgeFinset.erase e.1,
    (if extendActive G ω a then p else 1 - p)
  have hR : 0 ≤ R := by
    unfold R
    apply Finset.prod_nonneg
    intro a _
    split
    · exact hp.le
    · linarith
  have hk := numClusters_setClosed_le_setOpen_succ G e.1 (extendActive G ω)
  have hpow : q ^ numClusters G (setClosed e.1 (extendActive G ω)) ≤
      q * q ^ numClusters G (setOpen e.1 (extendActive G ω)) := by
    calc
      q ^ numClusters G (setClosed e.1 (extendActive G ω)) ≤
          q ^ (numClusters G (setOpen e.1 (extendActive G ω)) + 1) :=
        pow_le_pow_right₀ hq hk
      _ = q * q ^ numClusters G (setOpen e.1 (extendActive G ω)) := by
        rw [pow_succ]
        ring
  have hcoef : 0 ≤ p * (1 - p) * R := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hcoef]

lemma openMarginal_lower_of_open_pair {E : Type*} [Fintype E] [DecidableEq E]
    (μ : ConfigSpace E → ℝ) (hμ1 : ∑ ω, μ ω = 1) (e : E)
    {p q : ℝ} (hden : 0 < p + q * (1 - p))
    (hpair : ∀ ψ, p * μ (setClosed e ψ) ≤
      q * (1 - p) * μ (setOpen e ψ)) :
    p / (p + q * (1 - p)) ≤ openMarginal μ e := by
  let S := Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false)
  have hs := Finset.sum_le_sum fun ψ (_ : ψ ∈ S) => hpair ψ
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← openMarginal_eq_closedFiber] at hs
  have hone := activeClosedFiber_pairMass_eq_one μ hμ1 e
  change (∑ ψ ∈ S, (μ (setOpen e ψ) + μ (setClosed e ψ))) = 1 at hone
  rw [Finset.sum_add_distrib, ← openMarginal_eq_closedFiber] at hone
  have hclosed : (∑ ψ ∈ S, μ (setClosed e ψ)) = 1 - openMarginal μ e := by
    linarith
  rw [hclosed] at hs
  rw [div_le_iff₀ hden]
  nlinarith [hs]

theorem active_reducedDensity_le_openMarginal {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (e : G.edgeSet) :
    reducedDensity p q ≤ openMarginal (activeProb G (fun _ => p) q) e := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hden : 0 < p + q * (1 - p) := add_pos hp (mul_pos hq0 (by linarith))
  apply openMarginal_lower_of_open_pair _
    (activeProb_sum_eq_one G (fun _ => hp) (fun _ => hp1) hq0) e hden
  intro ψ
  unfold activeProb
  have hZ := activeZ_pos G (fun _ => hp) (fun _ => hp1) hq0
  rw [show p * (activeWeight G (fun _ => p) q (setClosed e ψ) /
      activeZ G (fun _ => p) q) =
      (p * activeWeight G (fun _ => p) q (setClosed e ψ)) /
        activeZ G (fun _ => p) q by ring]
  rw [show q * (1 - p) * (activeWeight G (fun _ => p) q (setOpen e ψ) /
      activeZ G (fun _ => p) q) =
      (q * (1 - p) * activeWeight G (fun _ => p) q (setOpen e ψ)) /
        activeZ G (fun _ => p) q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2
    (activeWeight_open_pair G hp hp1 hq e ψ)


end StatMech.BeffaraDC
