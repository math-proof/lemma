/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsTheoremAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties.Part2
import Lemma.Finset.SeparatedByWall.of.AdjacentToSimplicialComplex.HasSufficientReversibleFoldings
open AptIsCoxeterProof ChamberComplex

variable {V : Type*} [DecidableEq V]


/-- Tits theorem (Section 3.5): a thin chamber complex with sufficiently many
foldings is a Coxeter complex. Assembled by extracting a Coxeter matrix and
labeling map from the foldings hypothesis. -/
theorem tits_theorem_hyp : TitsTheoremHyp V := by
  intro cc hThin hSF
  obtain ⟨B_idx, M, φ, h_inj, h_surj, h_adj, _, _⟩ :=
    thinWithFoldings_isCoxeterComplex cc hThin hSF
  exact ⟨B_idx, M, φ, h_inj, h_surj, h_adj⟩

