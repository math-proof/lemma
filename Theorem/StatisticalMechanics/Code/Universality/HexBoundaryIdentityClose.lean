/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal
import Def.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose


namespace StatMech.Universality

open Complex Filter Topology

open scoped Real BigOperators Topology


theorem hbi_alphaPhase :
    (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
        + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2
      = ((-(hexBdryCl) : ℝ) : ℂ) := by
  have h2 : Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)
        + Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
      = 2 * (Real.cos (hbi_sigma * Real.pi) : ℂ) := hexExpI_add_neg (hbi_sigma * Real.pi)
  have hcos : Real.cos (hbi_sigma * Real.pi) = -hexBdryCl := by
    unfold hbi_sigma hexBdryCl
    rw [show (5 / 8 : ℝ) * Real.pi = Real.pi - 3 * Real.pi / 8 by ring, Real.cos_pi_sub]
  rw [add_comm, h2, hcos]
  push_cast; ring


theorem hbi_slantPhase :
    (hbi_j * Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
        + (starRingEnd ℂ) hbi_j
            * Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)) / 2
      = ((hexBdryCt : ℝ) : ℂ) := by
  
  have hjpos : hbi_j * Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
      = Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) := by
    unfold hbi_j hbi_sigma
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  have hjbarconj : (starRingEnd ℂ) hbi_j
      = Complex.exp ((-(2 * Real.pi / 3) : ℝ) * Complex.I) := by
    unfold hbi_j
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hjneg : (starRingEnd ℂ) hbi_j
        * Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)
      = Complex.exp ((-(Real.pi / 4) : ℝ) * Complex.I) := by
    rw [hjbarconj, ← Complex.exp_add]
    congr 1
    unfold hbi_sigma
    push_cast; ring
  rw [hjpos, hjneg]
  
  have h2 : Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)
        + Complex.exp ((-(Real.pi / 4) : ℝ) * Complex.I)
      = 2 * (Real.cos (Real.pi / 4) : ℂ) := hexExpI_add_neg (Real.pi / 4)
  rw [h2]
  unfold hexBdryCt
  push_cast; ring


theorem hbi_betaPhase :
    Complex.exp ((-(hbi_sigma * 0) : ℝ) * Complex.I) = 1 := by
  simp


end StatMech.Universality
