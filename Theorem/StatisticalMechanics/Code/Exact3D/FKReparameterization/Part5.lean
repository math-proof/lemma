/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5


namespace StatMech

namespace Exact3D

namespace FKReparameterization

set_option linter.style.longLine false in

theorem pOfBetaLeftPullbackWindow_pos
    (βc : ℝ) (pWindow : ℝ → ℝ)
    (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε)
    {ε : ℝ} (hε : 0 < ε) :
    0 < pOfBetaLeftPullbackWindow βc pWindow pWindow_pos ε := by
  have hspec :=
    Classical.choose_spec
      (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
        (pWindow_pos ε hε))
  simpa [pOfBetaLeftPullbackWindow, hε] using hspec.1

set_option linter.style.longLine false in

theorem pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
    (βc : ℝ) (pWindow : ℝ → ℝ)
    (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε)
    {ε β : ℝ} (hε : 0 < ε)
    (hβ :
      β ∈ Set.Ioo
        (βc - pOfBetaLeftPullbackWindow βc pWindow pWindow_pos ε) βc) :
    IsingFK.pOfBeta β ∈
      Set.Ioo (IsingFK.pOfBeta βc - pWindow ε) (IsingFK.pOfBeta βc) := by
  have hspec :=
    Classical.choose_spec
      (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
        (pWindow_pos ε hε))
  have hmap := hspec.2 β
  have hβ' :
      β ∈ Set.Ioo
        (βc -
          Classical.choose
            (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
              (pWindow_pos ε hε))) βc := by
    simpa [pOfBetaLeftPullbackWindow, hε] using hβ
  exact hmap hβ'


theorem hasCriticalNu_comp_pOfBeta {correlationLength : ℝ → ℝ} {βc ν : ℝ}
    (hν :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc))
        correlationLength ν) :
    HasCriticalNu (ParameterModel βc)
      (fun β => correlationLength (IsingFK.pOfBeta β)) ν :=
  hν.comp_leftCriticalReparam (pOfBeta_leftCriticalReparam βc)


theorem eventually_comp_pOfBeta_left {βc : ℝ} {P : ℝ → Prop}
    (hP :
      ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta βc)
          (Set.Iio (IsingFK.pOfBeta βc)),
        P p) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc), P (IsingFK.pOfBeta β) := by
  simpa [ParameterModel] using
    (pOfBeta_leftCriticalReparam βc).tendsto_left.eventually hP


theorem eventually_eq_comp_pOfBeta_left {βc : ℝ} {f g : ℝ → ℝ}
    (hEq :
      ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta βc)
          (Set.Iio (IsingFK.pOfBeta βc)),
        f p = g p) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      f (IsingFK.pOfBeta β) = g (IsingFK.pOfBeta β) :=
  eventually_comp_pOfBeta_left hEq


theorem hasCriticalNu_comp_pOfBeta_congr_eventually
    {βc ν : ℝ} {fkCorrelationLength comparisonLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc))
        fkCorrelationLength ν)
    (hEq :
      ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
        comparisonLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu (ParameterModel βc) comparisonLength ν :=
  (hasCriticalNu_comp_pOfBeta hfk).congr_eventually hEq

end FKReparameterization
end Exact3D
end StatMech
