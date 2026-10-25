/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApartmentsCoxeter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.List.All.of.All.IsChain.Ne
import Lemma.Nat.NotChamberAdjacent
import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace Building

/-- Two simplicial complexes on $V$ are isomorphic if there is a bijection
$\varphi : V \to V$ that induces a bijection between their face sets. -/
def SimplicialComplexIso (A A' : SimplicialComplex V) : Prop :=
  ∃ φ : V → V,
    Function.Bijective φ ∧
    (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)

/-- An apartment $A$ has foldings if its underlying simplicial complex
extends to a chamber complex on which every pair of adjacent chambers
admits a pair of foldings collapsing one chamber onto the other. -/
def ApartmentHasFoldings (b : Building V) (A : SimplicialComplex V)
    (_hA : A ∈ b.apartmentSystem.apartments) : Prop :=
  ∃ (cc : ChamberComplex V),
    cc.toSimplicialComplex = A ∧
    ∀ C C' : Finset V,
      A.Adjacent C C' →
      ∃ (f f' : Folding cc),
        C.image f.morph.toFun = C ∧ C'.image f.morph.toFun = C ∧
        C'.image f'.morph.toFun = C' ∧ C.image f'.morph.toFun = C'

end Building
