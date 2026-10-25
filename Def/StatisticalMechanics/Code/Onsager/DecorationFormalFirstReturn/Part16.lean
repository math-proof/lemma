/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part15


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decRootedExponentEquivAtomLists
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} ≃
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms ≠ [] ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} :=
  (Equiv.subtypeEquiv
    (ons_decRootedAtomEquivNonemptyAtoms L d)
    (fun root ↦ by
      rw [ons_decRootedAtomExponent_eq_atoms_sum])).trans <|
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun atoms : List (ons_DecFirstReturnAtom L d) ↦ atoms ≠ [])
      (fun atoms ↦ (atoms.map ons_decFirstReturnAtomExponent).sum = m)

noncomputable def ons_decAtomListsExponentEquivLength
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms ≠ [] ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} ≃
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms.length = m s(d, ons_dartRev L d) ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} :=
  Equiv.subtypeEquiv (Equiv.refl _)
    (fun atoms ↦ by
      constructor
      · rintro ⟨hne, hexponent⟩
        refine ⟨?_, hexponent⟩
        change atoms.length = m s(d, ons_dartRev L d)
        rw [← ons_decFirstReturnAtoms_externalExponent_sum L d atoms,
          hexponent]
      · rintro ⟨hlength, hexponent⟩
        refine ⟨?_, hexponent⟩
        intro hempty
        rw [hempty] at hlength
        simp at hlength
        omega)

noncomputable def ons_decAtomListsLengthEquivTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms.length = m s(d, ons_dartRev L d) ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun atoms : List (ons_DecFirstReturnAtom L d) ↦
        atoms.length = m s(d, ons_dartRev L d))
      (fun atoms ↦
        (atoms.map ons_decFirstReturnAtomExponent).sum = m)).symm |>.trans <|
    Equiv.subtypeEquiv
      (ons_listLengthEquivTuple (A := ons_DecFirstReturnAtom L d)
        (m s(d, ons_dartRev L d)))
      (fun atoms ↦ by
        let equiv := ons_listLengthEquivTuple
          (A := ons_DecFirstReturnAtom L d)
          (m s(d, ons_dartRev L d))
        have hlist := congrArg Subtype.val (equiv.symm_apply_apply atoms)
        change List.ofFn (equiv atoms) = atoms.1 at hlist
        change (atoms.1.map ons_decFirstReturnAtomExponent).sum = m ↔
          (∑ i, ons_decFirstReturnAtomExponent (equiv atoms i)) = m
        rw [← hlist, List.map_ofFn, List.sum_ofFn]
        rfl)

noncomputable def ons_decRootedExponentEquivUnboundedTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  (ons_decRootedExponentEquivAtomLists L d m).trans <|
    (ons_decAtomListsExponentEquivLength L d m hk).trans
      (ons_decAtomListsLengthEquivTuples L d m)

def ons_decForgetBoundedAtom
    {L N : ℕ} {d : ons_Dart L} :
    ons_DecFirstReturnAtomBounded L d N ↪
      ons_DecFirstReturnAtom L d :=
  Function.Embedding.sigmaMap Fin.valEmbedding
    (fun _ ↦ Function.Embedding.refl _)

end StatMech.Onsager
