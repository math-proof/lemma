/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Structure.StatisticalMechanics.Code.Universality.HexProjPhaseClose


namespace StatMech.Universality

open Complex

open scoped Real BigOperators


namespace hpp_BoundaryIntegralData

variable (D : hpp_BoundaryIntegralData)


theorem boundaryIntegral_eq :
    (1/2 : ℂ) * hexUnit 4 * D.alphaFSum
        + (1/2 : ℂ) * hexUnit 1 * D.betaFSum
        + ((1/2 : ℂ) * hexUnit 3 * D.epsFSum + (1/2 : ℂ) * hexUnit (-1) * D.epsbarFSum)
      = Complex.I * ((((hexBdryCl * D.A + hexBdryCt * D.E + D.B : ℝ) - (D.Fa : ℝ))/2 : ℝ) : ℂ) := by
  rw [D.alphaFSum_eq, D.betaFSum_eq, D.epsFSum_eq, D.epsbarFSum_eq]
  
  rw [show (1/2 : ℂ) * hexUnit 3
            * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * ((D.E/2 : ℝ) : ℂ))
          + (1/2 : ℂ) * hexUnit (-1)
            * (Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * ((D.E/2 : ℝ) : ℂ))
        = Complex.I * ((hexBdryCt * (D.E/2) : ℝ) : ℂ) from hpp_slantProj_combined D.E]
  
  rw [hpp_alphaDir, hpp_topDir]
  push_cast; ring


theorem boundaryIdentity (hFa : D.Fa = 1)
    (hvanish : (1/2 : ℂ) * hexUnit 4 * D.alphaFSum
        + (1/2 : ℂ) * hexUnit 1 * D.betaFSum
        + ((1/2 : ℂ) * hexUnit 3 * D.epsFSum + (1/2 : ℂ) * hexUnit (-1) * D.epsbarFSum) = 0) :
    hexBdryCl * D.A + hexBdryCt * D.E + D.B = 1 := by
  have heq := D.boundaryIntegral_eq
  rw [hvanish] at heq
  
  have hzero : (((hexBdryCl * D.A + hexBdryCt * D.E + D.B : ℝ) - (D.Fa : ℝ))/2 : ℝ) = 0 := by
    have : ((((hexBdryCl * D.A + hexBdryCt * D.E + D.B : ℝ) - (D.Fa : ℝ))/2 : ℝ) : ℂ) = 0 := by
      have h := heq.symm
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 Complex.I_ne_zero
      · exact h2
    exact_mod_cast this
  rw [hFa] at hzero
  linarith [hzero]

end hpp_BoundaryIntegralData


theorem hpp_hbdry (D : ℕ → hpp_BoundaryIntegralData)
    (hFa : ∀ v, 1 ≤ v → (D v).Fa = 1)
    (hvanish : ∀ v, 1 ≤ v →
      (1/2 : ℂ) * hexUnit 4 * (D v).alphaFSum
        + (1/2 : ℂ) * hexUnit 1 * (D v).betaFSum
        + ((1/2 : ℂ) * hexUnit 3 * (D v).epsFSum + (1/2 : ℂ) * hexUnit (-1) * (D v).epsbarFSum) = 0) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (D v).A + hexBdryCt * (D v).E + (D v).B = 1 := by
  intro v hv
  exact (D v).boundaryIdentity (hFa v hv) (hvanish v hv)


end StatMech.Universality
