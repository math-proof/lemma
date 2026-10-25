/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem hasDerivAt_fkProbWOf {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e)
    (hpf1 : ∀ e, pf e < 1) {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (A : Set (ConfigSpace (Sym2 V))) :
    HasDerivAt (fun t => fkProbWOf G (Function.update pf e₀ t) q A)
      (fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ)))
          (coordR e₀)
        / (pf e₀ * (1 - pf e₀)))
      (pf e₀) :=
  hasDerivAt_fkMeanW G hpf hpf1 hq he _


theorem deriv_fkProbWOf {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e)
    (hpf1 : ∀ e, pf e < 1) {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (A : Set (ConfigSpace (Sym2 V))) :
    deriv (fun t => fkProbWOf G (Function.update pf e₀ t) q A) (pf e₀)
      = fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ)))
          (coordR e₀)
        / (pf e₀ * (1 - pf e₀)) :=
  (hasDerivAt_fkProbWOf G hpf hpf1 hq he A).deriv


lemma hasDerivAt_paramOfBeta (J β : ℝ) :
    HasDerivAt (fun b => 1 - Real.exp (-(b * J))) (J * Real.exp (-(β * J))) β := by
  have h1 : HasDerivAt (fun b : ℝ => -(b * J)) (-J) β := by
    convert ((hasDerivAt_id β).mul_const J).neg using 1
    · ext b
      simp
    · simp
  have h2 : HasDerivAt (fun b => Real.exp (-(b * J))) (Real.exp (-(β * J)) * (-J)) β :=
    (Real.hasDerivAt_exp _).comp β h1
  have h3 := (hasDerivAt_const β (1 : ℝ)).sub h2
  convert h3 using 1
  ring


theorem hasDerivAt_fkProbWOf_beta {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e)
    (hpf1 : ∀ e, pf e < 1) {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (A : Set (ConfigSpace (Sym2 V))) (J β₀ : ℝ)
    (hpt : pf e₀ = 1 - Real.exp (-(β₀ * J))) :
    HasDerivAt
      (fun b => fkProbWOf G (Function.update pf e₀ (1 - Real.exp (-(b * J)))) q A)
      ((J / (1 - Real.exp (-(β₀ * J))))
        * fkCovW G (Function.update pf e₀ (pf e₀)) q
            (A.indicator (fun _ => (1 : ℝ))) (coordR e₀))
      β₀ := by
  have hinner := hasDerivAt_paramOfBeta J β₀
  have hval : (1 - Real.exp (-(β₀ * J))) = pf e₀ := hpt.symm
  
  have houter : HasDerivAt (fun t => fkProbWOf G (Function.update pf e₀ t) q A)
      (fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ)))
          (coordR e₀) / (pf e₀ * (1 - pf e₀)))
      (1 - Real.exp (-(β₀ * J))) := by
    rw [hval]; exact hasDerivAt_fkProbWOf G hpf hpf1 hq he A
  have hcomp := houter.comp β₀ hinner
  refine hcomp.congr_deriv ?_
  rw [hpt]
  set u := Real.exp (-(β₀ * J)) with hu
  have hupos : 0 < u := Real.exp_pos _
  have h1u : (0 : ℝ) < 1 - u := by
    have := hpf e₀; rw [hpt] at this; linarith
  have hune : u ≠ 0 := hupos.ne'
  have h1une : (1 : ℝ) - u ≠ 0 := h1u.ne'
  
  rw [show (1 : ℝ) - (1 - u) = u by ring]
  field_simp

end FK
end StatMech
