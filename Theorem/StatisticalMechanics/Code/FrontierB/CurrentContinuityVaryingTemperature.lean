/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityMagnetizationFK
import Theorem.StatisticalMechanics.Code.Ising.FreeStateDLR
import Mathlib.Topology.UniformSpace.CompactConvergence
open Filter MeasureTheory ProbabilityTheory MeasurableSpace Set Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction UniformConvergence


namespace StatMech.FrontierB

open ConfigSpace Ising Lattice

variable {d : Nat}


theorem continuous_fvWeight_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (tau : {x // x ∈ box d n} → Bool) :
    Continuous (fun z : Real × ConfigSpace (Site d) =>
      fvWeight z.2 n B z.1 h tau) := by
  unfold fvWeight
  exact Real.continuous_exp.comp
    (continuous_fst.neg.mul ((continuous_fvEnergy n B h tau).comp continuous_snd))

theorem continuous_fvZ_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real) :
    Continuous (fun z : Real × ConfigSpace (Site d) => fvZ z.2 n B z.1 h) := by
  unfold fvZ
  exact continuous_finsetSum _
    (fun tau _ => continuous_fvWeight_beta_boundary n B h tau)

theorem continuous_fvProb_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (tau : {x // x ∈ box d n} → Bool) :
    Continuous (fun z : Real × ConfigSpace (Site d) =>
      fvProb z.2 n B z.1 h tau) := by
  unfold fvProb
  exact (continuous_fvWeight_beta_boundary n B h tau).div
    (continuous_fvZ_beta_boundary n B h)
    (fun z => fvZ_ne_zero z.2 n B z.1 h)


theorem continuous_specApply_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (f : ConfigSpace (Site d) →ᵇ Real) :
    Continuous (fun z : Real × ConfigSpace (Site d) =>
      specApply n B z.1 h (f : ConfigSpace (Site d) → Real) z.2) := by
  have heq : (fun z : Real × ConfigSpace (Site d) =>
      specApply n B z.1 h (f : ConfigSpace (Site d) → Real) z.2) =
      fun z => ∑ tau : {x // x ∈ box d n} → Bool,
        fvProb z.2 n B z.1 h tau * f (glue z.2 tau) := by
    funext z
    exact specApply_eq_sum n B z.1 h f z.2
  rw [heq]
  exact continuous_finsetSum _ (fun tau _ =>
    (continuous_fvProb_beta_boundary n B h tau).mul
      (f.continuous.comp ((continuous_glue n tau).comp continuous_snd)))

end StatMech.FrontierB
