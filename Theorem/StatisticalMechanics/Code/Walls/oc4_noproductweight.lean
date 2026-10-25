/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc2_thetamatch.Part2
import Theorem.StatisticalMechanics.Code.Walls.oc3_noproductweight.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc3_core
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding

open StatMech.OSSS.GrandCoupling

open StatMech.OSSS.CovLowerBound

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc4_allF_match_meanMatch (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    ∀ g, expect ν g = Lindeberg.mean μ g :=
  fun g => (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν g).mp (hall g)


theorem oc4_allF_match_forces_uncorrelated (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) (e e' : E) (he : e ≠ e') :
    Lindeberg.cov μ (Lindeberg.coord e) (Lindeberg.coord e') = 0 :=
  oc3_match_forces_uncorrelated hν (oc4_allF_match_meanMatch μ hpos hμ1 σ ν hall) e e' he


theorem oc4_no_product_weight_expectAsCubeAt (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (hcorr : oc3_GenuinelyCorrelated μ) :
    ¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧
        ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f := by
  obtain ⟨e, e', he, hne⟩ := hcorr
  rintro ⟨ν, hν, hall⟩
  exact hne (oc4_allF_match_forces_uncorrelated μ hpos hμ1 σ hν hall e e' he)


theorem oc4_allF_match_not_genuinelyCorrelated (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    ¬ oc3_GenuinelyCorrelated μ := by
  rintro ⟨e, e', he, hne⟩
  exact hne (oc4_allF_match_forces_uncorrelated μ hpos hμ1 σ hν hall e e' he)


theorem oc4_allF_match_iff_weight_eq (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ) :
    (∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) ↔ (∀ ω, weight ν ω = μ ω) := by
  rw [← oc3_match_iff_weight_eq]
  constructor
  · exact fun hall g => (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν g).mp (hall g)
  · exact fun hmatch f => (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν f).mpr (hmatch f)


section FK

open StatMech.OSSS.MonotonicFK


theorem oc4_fk_no_product_weight_expectAsCubeAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (e e' : Sym2 V) (he : e ≠ e')
    (hfkg : Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0) :
    ¬ ∃ ν : Sym2 V → Bool → ℝ, IsProbWeight ν ∧
        ∀ f, oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f :=
  oc4_no_product_weight_expectAsCubeAt (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ ⟨e, e', he, hfkg⟩


theorem oc4_fk_allF_match_forces_uncorrelated {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    {ν : Sym2 V → Bool → ℝ} (hν : IsProbWeight ν)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f)
    (e e' : Sym2 V) (he : e ≠ e') :
    Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') = 0 :=
  oc4_allF_match_forces_uncorrelated (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ hν hall e e' he

end FK
end Walls
end StatMech
