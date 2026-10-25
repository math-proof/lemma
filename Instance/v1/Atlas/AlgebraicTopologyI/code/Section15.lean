/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.UnitInterval
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part9
open Topology


namespace SphereInfty

/-- **Proposition 15.5.** $S^{\infty}$ is contractible.

Proof: We compose the two homotopies $\text{const}_{e_1} \simeq T$ and
$T \simeq \text{id}$ to obtain $\text{const}_{e_1} \simeq \text{id}$, showing
the identity on $S^{\infty}$ is nullhomotopic. -/
instance contractibleSpace : ContractibleSpace Sphere := by
  rw [contractible_iff_id_nullhomotopic]
  have h1 : ContinuousMap.Homotopic TOnSphere (ContinuousMap.id Sphere) :=
    ⟨homotopy_T_to_id⟩
  have h2 : ContinuousMap.Homotopic constE1 TOnSphere :=
    ⟨homotopy_e1_to_T⟩
  exact ⟨⟨e1, e1_mem_sphere_set⟩, (h2.trans h1).symm⟩

end SphereInfty
