/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralSharp.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Theorem.StatisticalMechanics.Code.Onsager.KWWeighted.Part2


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


noncomputable def ons_KWcolumnMultiplier (L : Nat)
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2)
    (dart : ons_Dart L) : Complex :=
  ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) dart.2 *
    weight (ons_portEdge L dart)


end StatMech.Onsager
