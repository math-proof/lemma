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
import Def.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace Building

/-- The Coxeter type of a building: a Coxeter matrix $M$ together with the
data, for each apartment $A$, of a labeling of its chambers by the Coxeter
group $W(M)$ that is injective on chambers, surjective onto $W(M)$, and
sends adjacent chambers to $W(M)$-adjacent group elements. -/
structure CoxeterTypeOfBuilding (b : Building V) where
  B_idx : Type
  matrix : CoxeterMatrix B_idx
  apartments_iso : ∀ A ∈ b.apartmentSystem.apartments,
    ∃ (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      ∃ (φ : Finset V → matrix.Group),
        (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
        (∀ w : matrix.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
        (∀ C C', A.Adjacent C C' →
          CoxeterComplex.ChamberAdjacent matrix (φ C) (φ C'))

end Building
