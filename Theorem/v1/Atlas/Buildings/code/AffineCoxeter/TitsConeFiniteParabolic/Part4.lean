/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeFiniteParabolic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
import Mathlib.Order.Filter.Basic
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part3
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

variable (M : CoxeterMatrix B) [RootSystemData M]

/-- Evaluation at the standard basis vector $e_s$: $\langle e_s, x\rangle = x_s$. -/
theorem pairing_e (s : B) (x : B → ℝ) :
    pairing (CoxeterGroup.e s) x = x s := by
  simp only [pairing, CoxeterGroup.e, Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Singleton word: $\sigma_{[s]} = \sigma_s$. -/
theorem sigmaWord_singleton (s : B) (α : B → ℝ) :
    sigmaWord M [s] α = CoxeterGroup.sigma M s α := by
  simp [sigmaWord, List.foldl_cons, List.foldl_nil]

/-- Negation in the first argument: $\langle-\alpha, x\rangle = -\langle\alpha, x\rangle$. -/
theorem pairing_neg (α x : B → ℝ) :
    pairing (fun t => -(α t)) x = -(pairing α x) := by
  simp only [pairing, neg_mul, Finset.sum_neg_distrib]

/-- Sign-flip identity: $\langle e_s, \sigma^\vee_s y\rangle = -y_s$. -/
theorem pairing_e_dualSigma (s : B) (y : B → ℝ) :
    pairing (CoxeterGroup.e s) (dualSigma M s y) = -(y s) := by
  rw [pairing_dualSigma_eq_sigma_pairing]
  rw [CoxeterGroup.sigma_e_self]
  rw [pairing_neg, pairing_e]

/-- If $y_s < 0$ and $e_s \in \Phi^+$, then $e_s$ belongs to the set of positive roots
with nonpositive pairing at $y$. -/
theorem e_mem_nonposRoots_of_neg [RootSystemData M] (s : B) (y : B → ℝ) (hs : y s < 0)
    (he_mem : CoxeterGroup.e s ∈ RootSystemData.Φpos (M := M)) :
    CoxeterGroup.e s ∈ nonposRoots (RootSystemData.Φpos (M := M)) y :=
  ⟨he_mem, by rw [pairing_e]; exact le_of_lt hs⟩

/-- The simple root $e_s$ is not in the image of $\sigma_s$ on the nonposRoots of
$\sigma^\vee_s y$, used to obtain a strict cardinality drop in the induction. -/
theorem e_not_in_sigmaWord_image [RootSystemData M] (s : B) (y : B → ℝ) (hs : y s < 0) :
    CoxeterGroup.e s ∉ sigmaWord M [s] '' nonposRoots (RootSystemData.Φpos (M := M)) (dualSigma M s y) := by
  intro ⟨α, ⟨hαΦ, _⟩, hαeq⟩


  rw [sigmaWord_singleton] at hαeq
  have hα_eq : α = CoxeterGroup.sigma M s (CoxeterGroup.e s) := by
    have := congr_arg (CoxeterGroup.sigma M s) hαeq
    rwa [sigma_involutive] at this

  rw [hα_eq, CoxeterGroup.sigma_e_self] at hαΦ


  have h_inv := RootSystemData.simple_inversion (M := M) s
  have h_es : CoxeterGroup.e s ∈ ({CoxeterGroup.e s} : Set (B → ℝ)) := Set.mem_singleton _
  rw [← h_inv] at h_es
  exact h_es.2 (by rwa [sigmaWord_singleton, CoxeterGroup.sigma_e_self])

/-- Converse direction of the Tits cone characterisation: any $x \neq 0$ satisfying
nu-finiteness lies in $U$. The proof inducts on the cardinality of the nonposRoots set,
using a simple reflection at a negative coordinate to strictly shrink it. -/
theorem nuFinite_mem_titsCone (x : B → ℝ) (_hx : x ≠ 0)
    (hnu : nuFiniteAt (RootSystemData.Φpos (M := M)) x) :
    x ∈ titsConeSet M := by
  sorry

end TitsCone
