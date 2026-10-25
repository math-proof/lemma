/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Def.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part6
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptMConditional

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.LindebergTree OSSS.AdaptiveTau

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma integral_truncInd_eq_reveal (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (i : Fin n) :
    (∫ p, truncInd μ σ f p.1 ((i : ℕ) + 1) ∂((Vcube n).prod (Vcube n)))
      = revealAdapt μ σ f ((σ : Fin n → E) i) := by
  unfold revealAdapt
  rw [Equiv.symm_apply_apply]


theorem tree_osss_sharp_unconditional {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) (hStep : AdaptStepCovBound μ σ f) :
    Lindeberg.var μ f
      ≤ ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) := by
  
  refine (var_le_trunc_telescope hpos hμ1 σ hf0 hf1).trans ?_
  
  rw [Finset.mul_sum]
  
  have hstepbnd : ∀ i : Fin n,
      (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
              - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
              * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n))
        ≤ revealAdapt μ σ f ((σ : Fin n → E) i)
            * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) := by
    intro i
    have hb := hStep (i : ℕ) i.2
    have hi : (⟨(i:ℕ), i.2⟩ : Fin n) = i := Fin.ext rfl
    rw [hi] at hb
    rw [integral_truncInd_eq_reveal μ σ f i] at hb
    
    have : (1/2 : ℝ) * (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
              - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
              * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n)))
        ≤ (1/2) * (2 * (Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i))
            * revealAdapt μ σ f ((σ : Fin n → E) i))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    calc (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
              - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
              * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n))
        ≤ (1/2) * (2 * (Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i))
            * revealAdapt μ σ f ((σ : Fin n → E) i))) := this
      _ = revealAdapt μ σ f ((σ : Fin n → E) i)
            * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) := by ring
  calc ∑ t ∈ Finset.range n,
        (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n))
      = ∑ i : Fin n,
          (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
                  - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
                  * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n)) := by
        rw [Finset.sum_range (fun t =>
          (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                  - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                  * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)))]
    _ ≤ ∑ i : Fin n, revealAdapt μ σ f ((σ : Fin n → E) i)
            * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) :=
        Finset.sum_le_sum (fun i _ => hstepbnd i)
    _ = ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) :=
        Equiv.sum_comp σ (fun e => revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e))


section FK

open StatMech.OSSS.MonotonicFK


theorem fk_q2_osss_sharp_unconditional {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hStep : AdaptStepCovBound (fkMass G p 2) σ f) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, revealAdapt (fkMass G p 2) σ f e
          * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  tree_osss_sharp_unconditional
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num)) σ hf0 hf1 hStep

end FK
end AdaptMConditional
end OSSS
end StatMech
