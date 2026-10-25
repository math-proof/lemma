/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiscreteFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.UniqueRetraction
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import Lemma.Finset.Any_And_All_EqAndAll_IsMaximalAndAll_EqImageSOrAdjacentAndAll_Eq.of.IsMaximal.In_Apartments
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization.Part2
import Theorem.v1.Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
set_option linter.unusedSectionVars false


noncomputable section

open Finset BigOperators

/-- The simplicial complex consisting of all non-empty subsets of a fixed
chamber $C$ — the abstract closure of the simplex $C$. -/
def closureSC {V : Type} [DecidableEq V] (C : Finset V) (hC : C.Nonempty) :
    SimplicialComplex V where
  faces := { s : Finset V | s ⊆ C ∧ s.Nonempty }
  nonempty_of_mem := fun s hs => hs.2
  down_closed := fun {s t} hs ht hne => ⟨ht.trans hs.1, hne⟩

end
