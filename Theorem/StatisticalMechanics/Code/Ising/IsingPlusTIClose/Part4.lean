/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem iti_plusMultiHomogeneous_one (β h : ℝ) :
    iti_PlusMultiHomogeneous β h (1 : Multiplicative (Site d)) := by
  intro T
  have hTeq : T.image (fun x => (1 : Multiplicative (Site d))⁻¹ • x) = T := by
    rw [Finset.image_congr (g := id) (fun x _ => by simp), Finset.image_id]
  rw [hTeq]


theorem iti_decayFun_monomial_tendsto_zero (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hhom : iti_PlusMultiHomogeneous β h g) (T : Finset (Site d)) :
    Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (iti_monomialBcf T))
      atTop (𝓝 0) := by
  have hdecay : pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (iti_monomialBcf T)
      = fun n =>
        ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            (fmu_multiOpen (E := Site d) T))
          - ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
              (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) := by
    funext n; exact iti_decayFun_monomial _ g T n
  rw [hdecay]
  have h1 := iti_plus_multiOpen_tendsto β h φ T hconv
  have h2 := iti_plus_multiOpen_tendsto β h φ (T.image (fun x => g⁻¹ • x)) hconv
  have hsub := h1.sub h2
  rw [← hhom T, sub_self] at hsub
  exact hsub


theorem iti_decayFun_add (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f f' : ConfigSpace (Site d) →ᵇ ℝ) (n : ℕ) :
    pstc_decayFun μ g (f + f') n = pstc_decayFun μ g f n + pstc_decayFun μ g f' n := by
  simp only [pstc_decayFun, BoundedContinuousFunction.coe_add, Pi.add_apply]
  have h1 : (∫ x, (f x + f' x) ∂(μ n : Measure _))
      = (∫ x, f x ∂(μ n : Measure _)) + ∫ x, f' x ∂(μ n : Measure _) :=
    integral_add (f.integrable _) (f'.integrable _)
  have h2 : (∫ x, (f (shift g x) + f' (shift g x)) ∂(μ n : Measure _))
      = (∫ x, f (shift g x) ∂(μ n : Measure _)) + ∫ x, f' (shift g x) ∂(μ n : Measure _) :=
    integral_add ((f.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
      ((f'.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
  rw [h1, h2]; ring


theorem iti_decayFun_smul (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (c : ℝ) (f : ConfigSpace (Site d) →ᵇ ℝ) (n : ℕ) :
    pstc_decayFun μ g (c • f) n = c * pstc_decayFun μ g f n := by
  simp only [pstc_decayFun, BoundedContinuousFunction.coe_smul, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]; ring


theorem iti_decayFun_zero (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (n : ℕ) :
    pstc_decayFun μ g (0 : ConfigSpace (Site d) →ᵇ ℝ) n = 0 := by
  simp only [pstc_decayFun, BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero,
    sub_zero]


end Ising
end StatMech
