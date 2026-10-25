/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptIsCoxeterProof.lean -/

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
import Mathlib.GroupTheory.Coxeter.Length
import Structure.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
set_option maxHeartbeats 0

open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace AptIsCoxeterProof

/-- Uniqueness of labellings on an apartment: any two strict-mono labellings agree up to a unique
bijection of label sets determined by the value on a fixed chamber $C_0$. -/
def HasSufficientFoldings (cc : ChamberComplex V) : Prop :=
  ∀ C C' : Finset V,
    cc.toSimplicialComplex.Adjacent C C' →
    ∃ (f f' : Folding cc),
      C.image f.morph.toFun = C ∧ C'.image f.morph.toFun = C ∧
      C'.image f'.morph.toFun = C' ∧ C.image f'.morph.toFun = C'

/-- Hypothesis statement of Tits' theorem: every thin chamber complex with sufficient foldings is
isomorphic to a Coxeter complex. -/
def TitsTheoremHyp (V : Type*) [DecidableEq V] : Prop :=
  ∀ (cc : ChamberComplex V),
    cc.IsThin → HasSufficientFoldings cc →
    ∃ (B_idx : Type) (M : CoxeterMatrix B_idx)
      (φ : Finset V → M.Group),
      (∀ C, cc.toSimplicialComplex.IsMaximal C →
        ∀ D, cc.toSimplicialComplex.IsMaximal D →
          φ C = φ D → C = D) ∧
      (∀ w : M.Group, ∃ C, cc.toSimplicialComplex.IsMaximal C ∧ φ C = w) ∧
      (∀ C C', cc.toSimplicialComplex.Adjacent C C' →
        CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))

/-- Hypothesis statement: in a thick chamber complex, every apartment carries a thin chamber
structure with sufficient foldings. -/
def ThicknessImpliesAptStructureHyp (V : Type*) [DecidableEq V] : Prop :=
  ∀ (K : ChamberComplex V),
    K.IsThick →
    ∀ (pre : PreApartmentData K) (A : SimplicialComplex V),
      A ∈ pre.apartments →
      ∃ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A ∧
        cc.IsThin ∧
        HasSufficientFoldings cc

end AptIsCoxeterProof
