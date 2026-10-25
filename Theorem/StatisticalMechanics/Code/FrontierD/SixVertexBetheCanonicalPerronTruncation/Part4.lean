/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexCanonicalRegularizationUpper
    {c epsilon eta : Real} (hc0 : c ≠ 0) (heta : 0 < eta) :
    Tendsto (sixVertexCanonicalRegularizationUpper c epsilon eta)
      atTop (nhds (sixVertexCanonicalRegularizationEnvelope c epsilon eta)) := by
  let x : Nat -> Real := fun k =>
    (sixVertexCanonicalLinearEdgeCutoff eta k : Real) /
      (sixVertexFourWidth 0 k : Real)
  have hx : Tendsto x atTop (nhds eta) :=
    tendsto_sixVertexCanonicalLinearEdgeCutoff_ratio heta.le
  have htwo : Tendsto (fun k => 2 * x k) atTop (nhds (2 * eta)) :=
    hx.const_mul 2
  have hratio : Tendsto (fun k => c ^ 2 / (2 * x k)) atTop
      (nhds (c ^ 2 / (2 * eta))) :=
    tendsto_const_nhds.div htwo (by positivity)
  have hlog : Tendsto (fun k => Real.log (c ^ 2 / (2 * x k))) atTop
      (nhds (Real.log (c ^ 2 / (2 * eta)))) :=
    hratio.log (div_ne_zero (pow_ne_zero 2 hc0)
      (by positivity))
  have hfirst : Tendsto (fun k =>
      2 * x k * (Real.log (c ^ 2 / (2 * x k)) + 1)) atTop
      (nhds (2 * eta * (Real.log (c ^ 2 / (2 * eta)) + 1))) :=
    htwo.mul (hlog.add tendsto_const_nhds)
  have hfour : Tendsto (fun k => 4 * x k) atTop (nhds (4 * eta)) :=
    hx.const_mul 4
  have hsecond : Tendsto (fun k => epsilon / (4 * x k)) atTop
      (nhds (epsilon / (4 * eta))) :=
    tendsto_const_nhds.div hfour (by positivity)
  simpa only [sixVertexCanonicalRegularizationUpper,
    sixVertexCanonicalRegularizationEnvelope, x] using hfirst.add hsecond

theorem sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper
    {c epsilon eta : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4)
    (heta : 0 < eta) (hetaUpper : eta <= 1 / 4) (k : Nat) :
    sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c epsilon) k <=
      sixVertexCanonicalRegularizationUpper c epsilon eta k := by
  let J := sixVertexCanonicalLinearEdgeCutoff eta k
  let N : Real := sixVertexFourWidth 0 k
  let x : Real := (J : Real) / N
  have hJ : 0 < J := sixVertexCanonicalLinearEdgeCutoff_pos heta k
  have hJle : J <= k + 1 :=
    sixVertexCanonicalLinearEdgeCutoff_le hetaUpper k
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hJreal : (0 : Real) < J := by exact_mod_cast hJ
  have hx : 0 < x := div_pos hJreal hN
  have hmaster :=
    (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc hepsilon hepsilonUpper hJ k).2
  have hinitial :=
    sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling
      hc hJ hJle
  have hratio : c ^ 2 * N / (2 * (J : Real)) = c ^ 2 / (2 * x) := by
    dsimp [x]
    field_simp [hN.ne', hJreal.ne']
  calc
    _ <= sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
        epsilon * N / (4 * (J : Real)) := hmaster
    _ <= (2 * (J : Real) *
          (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N +
        epsilon * N / (4 * (J : Real)) := by gcongr
    _ = sixVertexCanonicalRegularizationUpper c epsilon eta k := by
      rw [hratio]
      unfold sixVertexCanonicalRegularizationUpper
      change _ = 2 * x * (Real.log (c ^ 2 / (2 * x)) + 1) +
        epsilon / (4 * x)
      dsimp [x]
      field_simp [hN.ne', hJreal.ne', hx.ne']

end
end StatMech.FrontierD
