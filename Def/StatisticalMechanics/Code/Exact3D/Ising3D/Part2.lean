/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D
open MeasureTheory


namespace StatMech

namespace Exact3D

open StatMech.Lattice


noncomputable def ising3DPlusTwoPoint (β : ℝ) (x y : Ising3DSite) : ℝ :=
  ∫ ω : ConfigSpace Ising3DSite,
    Ising.spin ω x * Ising.spin ω y
      ∂(Ising.plusState 3 β 0 : Measure (ConfigSpace Ising3DSite))


noncomputable def ising3DFreeTwoPoint (β : ℝ) (x y : Ising3DSite) : ℝ :=
  ∫ ω : ConfigSpace Ising3DSite,
    Ising.spin ω x * Ising.spin ω y
      ∂(Ising.freeState 3 β 0 : Measure (ConfigSpace Ising3DSite))


noncomputable def twoPointAtDisplacement (β : ℝ) (x : Ising3DSite) : ℝ :=
  ising3DPlusTwoPoint β ising3DOrigin x


noncomputable def twoPointOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  twoPointAtDisplacement β (ising3DXAxisRay n)


noncomputable def freeTwoPointAtDisplacement (β : ℝ) (x : Ising3DSite) : ℝ :=
  ising3DFreeTwoPoint β ising3DOrigin x


noncomputable def freeTwoPointOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  freeTwoPointAtDisplacement β (ising3DXAxisRay n)

end Exact3D
end StatMech
