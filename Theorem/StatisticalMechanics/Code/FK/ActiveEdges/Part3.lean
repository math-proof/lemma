/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Def.StatisticalMechanics.Code.FK.ActiveEdges.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


section Fiber

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma openMarginal_eq_closedFiber (μ : ConfigSpace E → ℝ) (e : E) :
    openMarginal μ e =
      ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false), μ (setOpen e ψ) := by
  unfold openMarginal
  apply Finset.sum_nbij' (fun ω => setClosed e ω) (fun ψ => setOpen e ψ)
  · intro ω _
    simp [setClosed]
  · intro ψ _
    simp [setOpen]
  · intro ω hω
    simp only [Finset.mem_filter] at hω
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hω.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ψ hψ
    simp only [Finset.mem_filter] at hψ
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hψ.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ω hω
    simp only [Finset.mem_filter] at hω
    congr 1
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hω.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]

lemma activeClosedFiber_pairMass_eq_one (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (e : E) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false),
      (μ (setOpen e ψ) + μ (setClosed e ψ)) = 1 := by
  rw [Finset.sum_add_distrib, ← openMarginal_eq_closedFiber]
  have hclosed : (∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false),
      μ (setClosed e ψ)) =
      ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace E => ω e = false), μ ω := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp only [Finset.mem_filter] at hψ
    congr 1
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hψ.2]
    · simp [setClosed_of_ne hx]
  rw [hclosed]
  unfold openMarginal
  rw [show Finset.univ.filter (fun ω : ConfigSpace E => ω e = false) =
      Finset.univ.filter (fun ω : ConfigSpace E => ¬ ω e = true) by ext ω; simp]
  rw [Finset.sum_filter_add_sum_filter_not]
  exact hμ1

lemma openMarginal_le_of_close_pair (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (e : E) {p : ℝ}
    (hpair : ∀ ψ, (1 - p) * μ (setOpen e ψ) ≤ p * μ (setClosed e ψ)) :
    openMarginal μ e ≤ p := by
  let S := Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false)
  have hsum := Finset.sum_le_sum (fun ψ (_ : ψ ∈ S) => hpair ψ)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [← openMarginal_eq_closedFiber μ e] at hsum
  have hpair1 := activeClosedFiber_pairMass_eq_one μ hμ1 e
  change (∑ ψ ∈ S, (μ (setOpen e ψ) + μ (setClosed e ψ))) = 1 at hpair1
  rw [Finset.sum_add_distrib, ← openMarginal_eq_closedFiber μ e] at hpair1
  calc
    openMarginal μ e = (1 - p) * openMarginal μ e + p * openMarginal μ e := by ring
    _ ≤ p * (∑ ψ ∈ S, μ (setClosed e ψ)) + p * openMarginal μ e :=
      by simpa [add_comm] using add_le_add_right hsum (p * openMarginal μ e)
    _ = p := by rw [← mul_add, add_comm, hpair1, mul_one]

end Fiber

theorem active_openMarginal_le_param {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (e : G.edgeSet) :
    openMarginal (activeProb G pf q) e ≤ pf e.1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply openMarginal_le_of_close_pair _
    (activeProb_sum_eq_one G hpf hpf1 hq0) e
  intro ψ
  unfold activeProb
  have hZ : 0 < activeZ G pf q := activeZ_pos G hpf hpf1 hq0
  rw [show (1 - pf e.1) * (activeWeight G pf q (setOpen e ψ) / activeZ G pf q) =
      ((1 - pf e.1) * activeWeight G pf q (setOpen e ψ)) / activeZ G pf q by ring]
  rw [show pf e.1 * (activeWeight G pf q (setClosed e ψ) / activeZ G pf q) =
      (pf e.1 * activeWeight G pf q (setClosed e ψ)) / activeZ G pf q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2
    (activeWeight_close_pair G hpf hpf1 hq e ψ)

end FK
end StatMech
