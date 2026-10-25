/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction
open Set SimpleGraph
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

noncomputable section

theorem mixedDualComplementRN_isEmpty_of_all_connected
    (D : SymmetricDomain) (q : Real)
    (hall : ∀ omega, D.MixedConnected omega) :
    IsEmpty (MixedDualComplementRN D q) := by
  constructor
  intro R
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hdual : D.MixedConnected (R.dual omega) := hall _
  have hnot : ¬D.MixedConnected omega :=
    (R.connected_dual_iff omega).mp hdual
  exact hnot (hall omega)


theorem mixedDualComplementRN_isEmpty_of_all_disconnected
    (D : SymmetricDomain) (q : Real)
    (hall : ∀ omega, ¬D.MixedConnected omega) :
    IsEmpty (MixedDualComplementRN D q) := by
  constructor
  intro R
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hdual : D.MixedConnected (R.dual omega) :=
    (R.connected_dual_iff omega).mpr (hall omega)
  exact hall (R.dual omega) hdual


theorem degenerate_openConnected_all
    (omega : ConfigSpace (Sym2 degenerateSymmetricDomain.Vertex)) :
    degenerateSymmetricDomain.OpenConnected omega := by
  let x := degenerateSymmetricDomain.gammaOneStart
  let y := degenerateSymmetricDomain.gammaTwoStart
  have hxy : x = y := Subtype.ext (by rfl)
  refine ⟨x, y, onGammaOne_gammaOneStart _,
    onGammaTwo_gammaTwoStart _, ?_⟩
  rw [hxy]


theorem degenerate_mixedConnected_all
    (omega : ConfigSpace (Sym2 degenerateSymmetricDomain.Vertex)) :
    degenerateSymmetricDomain.MixedConnected omega :=
  (mixedConnected_iff_openConnected degenerateSymmetricDomain omega).2
    (degenerate_openConnected_all omega)


theorem degenerate_mixedDualComplementRN_isEmpty (q : Real) :
    IsEmpty (MixedDualComplementRN degenerateSymmetricDomain q) :=
  mixedDualComplementRN_isEmpty_of_all_connected
    degenerateSymmetricDomain q degenerate_mixedConnected_all


end
end SymmetricDomain
end BeffaraDC
end StatMech
