/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def exactMonomialEpsilonTable
    (C : RGCertificate Ising3DModel)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    EpsilonTable C (exactMonomialFKMass C) Unit epsilon := by
  classical
  let lowerRat : ℚ :=
    Classical.choose
      (exists_rat_btwn (sub_lt_self C.predictedExponent hepsilon))
  have hlowerRat_spec :
      C.predictedExponent - epsilon < (lowerRat : ℝ) ∧
        (lowerRat : ℝ) < C.predictedExponent := by
    simpa [lowerRat] using
      Classical.choose_spec
        (exists_rat_btwn (sub_lt_self C.predictedExponent hepsilon))
  let upperRat : ℚ :=
    Classical.choose
      (exists_rat_btwn (lt_add_of_pos_right C.predictedExponent hepsilon))
  have hupperRat_spec :
      C.predictedExponent < (upperRat : ℝ) ∧
        (upperRat : ℝ) < C.predictedExponent + epsilon := by
    simpa [upperRat] using
      Classical.choose_spec
        (exists_rat_btwn (lt_add_of_pos_right C.predictedExponent hepsilon))
  let interval : RatInterval :=
    { lower := lowerRat
      upper := upperRat
      lower_le_upper := by
        exact_mod_cast le_of_lt
          (lt_trans hlowerRat_spec.2 hupperRat_spec.1) }
  exact
    { table :=
        { cases := {()}
          interval := fun _ => interval }
      classify := fun _ => ()
      window := (1 : ℝ) / 2
      window_pos := by norm_num
      covers_on_Ioo := by
        intro _ _
        simp
      sound_on_Ioo := by
        intro p hp
        have hvalue := logRatioValue_exactMonomialFKMass C hp
        dsimp [interval]
        rw [hvalue]
        exact ⟨le_of_lt hlowerRat_spec.2, le_of_lt hupperRat_spec.1⟩
      lower_inside_slack := by
        intro _ _
        simpa [interval] using hlowerRat_spec.1
      upper_inside_slack := by
        intro _ _
        simpa [interval] using hupperRat_spec.2 }

set_option linter.style.longLine false in


noncomputable def exactMonomialCertificate
    (C : RGCertificate Ising3DModel) :
    Certificate C (exactMonomialFKMass C) Unit where
  pδ := (1 : ℝ) / 2
  pδ_pos := by norm_num
  fkMass_pos := by
    intro _ _
    exact Real.exp_pos _
  epsilonTable := exactMonomialEpsilonTable C

set_option linter.style.longLine false in


noncomputable def constantPrefactorMonomialFKMass
    (C : RGCertificate Ising3DModel) (A : ℝ) : ℝ → ℝ :=
  fun p => A * exactMonomialFKMass C p

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
