/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexNormalizedBethePairFactorAt (k : Nat)
    (i j : Fin ((k + 1) + (k + 1))) :
    Tendsto
      (fun c => sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c))
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)))
      atTop (nhds (sixVertexHalfFilledLimitingPhase k i)) := by
  let u : Real -> Complex := fun c =>
    sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c)
  let v : Real -> Complex := fun c =>
    sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)
  let u0 := sixVertexHalfFilledLimitingPhase k i
  let v0 := sixVertexHalfFilledLimitingPhase k j
  have hu : Tendsto u atTop (nhds u0) :=
    tendsto_sixVertexHalfFilledBethePhaseAt k i
  have hv : Tendsto v atTop (nhds v0) :=
    tendsto_sixVertexHalfFilledBethePhaseAt k j
  have hinvR : Tendsto (fun c : Real => 1 / (c ^ 2 - 2))
      atTop (nhds 0) := tendsto_sixVertexPairScale.const_div_atTop 1
  have hinvC : Tendsto
      (fun c : Real => Complex.ofReal (1 / (c ^ 2 - 2)))
      atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
  have hlimit : Tendsto
      (fun c => u c + (1 + u c * v c) *
        Complex.ofReal (1 / (c ^ 2 - 2)))
      atTop (nhds u0) := by
    simpa using hu.add ((tendsto_const_nhds.add (hu.mul hv)).mul hinvC)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
  have hdC : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by exact_mod_cast hd
  have hinv : Complex.ofReal (1 / (c ^ 2 - 2)) *
      ((c ^ 2 - 2 : Real) : Complex) = 1 := by
    rw [← Complex.ofReal_mul]
    field_simp [hd]
    norm_num
  dsimp [u, v]
  unfold sixVertexNormalizedBethePairFactor
  rw [eq_div_iff hdC]
  symm
  calc
    sixVertexBethePairFactor c
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c))
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)) =
      1 + sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) *
          sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c) +
        ((c ^ 2 - 2 : Real) : Complex) *
          sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) := by
        unfold sixVertexBethePairFactor sixVertexDelta
        push_cast
        ring
    _ = (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) +
          (1 + sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) *
            sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)) *
              Complex.ofReal (1 / (c ^ 2 - 2))) *
        ((c ^ 2 - 2 : Real) : Complex) := by
      rw [add_mul, mul_assoc, hinv, mul_one]
      ring


end
end StatMech.FrontierD
