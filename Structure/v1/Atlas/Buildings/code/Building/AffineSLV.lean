/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.Building.AffineSLV
set_option linter.unusedSectionVars false


namespace AffineBuildingSLV

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- A simplex of the Bruhat-Tits building of $SL_V$ is a finite set of pairwise
incident homothety classes of $\mathfrak{o}$-lattices in $V$. -/
structure Simplex where
  vertices : Finset (DVRContext.HomothetyClass C)
  mutually_incident : ∀ ξ ∈ vertices, ∀ η ∈ vertices, IncidenceRel C ξ η

/-- A line in $V = k^n$ is a one-dimensional subspace, represented here by a
nonzero generator. -/
structure Line where
  generator : Fin C.n → C.k
  generator_ne_zero : generator ≠ 0

/-- A frame in $V = k^n$ is an ordered family of $n$ lines that spans $V$
and is linearly independent: a decomposition $V = L_1 \oplus \cdots \oplus
L_n$ into lines. -/
structure Frame where
  lines : Fin C.n → Line C
  spans : ∀ v : Fin C.n → C.k,
    ∃ coeffs : Fin C.n → C.k,
      v = fun i => ∑ j, coeffs j * (lines j).generator i
  independent : ∀ coeffs : Fin C.n → C.k,
    (fun i => ∑ j : Fin C.n, coeffs j * (lines j).generator i) = 0 →
    ∀ j, coeffs j = 0

end AffineBuildingSLV
