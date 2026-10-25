/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Structure.StatisticalMechanics.Code.Universality.HexBoundary


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


namespace HexDomain

variable {V : Type*} [DecidableEq V] (D : HexDomain V)


noncomputable def incTerm (e : HexIncidence V) : ℂ :=
  (D.mid e.vtx e.edge - D.pos e.vtx) * D.obs (D.mid e.vtx e.edge)


noncomputable def incidences : Finset (HexIncidence V) :=
  D.interiorVertices ×ˢ (Finset.univ : Finset (Fin 3))
    |>.image (fun p => ⟨p.1, p.2⟩)


noncomputable def globalSum : ℂ :=
  ∑ v ∈ D.interiorVertices, ∑ j : Fin 3, D.incTerm ⟨v, j⟩

end HexDomain
end StatMech.Universality
