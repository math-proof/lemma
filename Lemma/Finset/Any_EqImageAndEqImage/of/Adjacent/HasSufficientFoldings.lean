import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.WallReflectionAction
open ChamberComplex AptIsCoxeterProof WallReflectionAction


/--
[adj_folding_fix_fold](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/WallReflectionAction.lean)
-/
@[path]
lemma adj_folding_fix_fold
  [DecidableEq V]
  {cc : ChamberComplex V}
  {C D : Finset V}
-- given
  (hsf : HasSufficientFoldings cc)
  (hadj : cc.toSimplicialComplex.Adjacent C D) :
-- imply
  ∃ (f : Folding cc), C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C :=
-- proof
  TitsTheoremProof.sufficient_foldings_fix_fold cc hsf C D hadj


private lemma gallery_step_has_folding
  [DecidableEq V]
  {cc : ChamberComplex V}
  {C D : Finset V}
-- given
  (hsf : HasSufficientFoldings cc)
  (hadj : cc.toSimplicialComplex.Adjacent C D) :
-- imply
  ∃ (f : Folding cc), C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C :=
-- proof
  adj_folding_fix_fold hsf hadj


private lemma gallery_chain_head_adj
  [DecidableEq V]
  {cc : ChamberComplex V}
  {a b : Finset V}
  {rest : List (Finset V)}
-- given
  (hchain : List.IsChain cc.toSimplicialComplex.Adjacent (a :: b :: rest)) :
-- imply
  cc.toSimplicialComplex.Adjacent a b := by
-- proof
  rw [List.isChain_cons] at hchain
  exact hchain.1 b rfl


private lemma gallery_chain_tail
  [DecidableEq V]
  {cc : ChamberComplex V}
  {a b : Finset V}
  {rest : List (Finset V)}
-- given
  (hchain : List.IsChain cc.toSimplicialComplex.Adjacent (a :: b :: rest)) :
-- imply
  List.IsChain cc.toSimplicialComplex.Adjacent (b :: rest) := by
-- proof
  rwa [List.isChain_cons] at hchain


private lemma isChain_getElem_adj
  [DecidableEq V]
  {R : α → α → Prop}
  {l : List α}
  {i : ℕ}
-- given
  (hchain : List.IsChain R l)
  (hi : i + 1 < l.length) :
-- imply
  R l[i] l[i + 1] := by
-- proof
  rw [List.isChain_iff_getElem] at hchain
  exact hchain i hi


private lemma chain_foldings_exist
  [DecidableEq V]
  {cc : ChamberComplex V}
  {cs : List (Finset V)}
-- given
  (hsf : HasSufficientFoldings cc)
  (hchain : List.IsChain cc.toSimplicialComplex.Adjacent cs)
  (hall : ∀ C ∈ cs, cc.toSimplicialComplex.IsMaximal C) :
-- imply
  ∃ (fs : List (Folding cc)), fs.length + 1 = cs.length ∨ (cs.length = 0 ∧ fs = []) := by
-- proof
  match cs with
  | [] => exact ⟨[], Or.inr ⟨rfl, rfl⟩⟩
  | [_] => exact ⟨[], Or.inl (by simp)⟩
  | a :: b :: rest =>
    have hadj := gallery_chain_head_adj hchain
    have htail := gallery_chain_tail hchain
    obtain ⟨f, _, _⟩ := gallery_step_has_folding hsf hadj
    obtain ⟨fs_tail, htail_prop⟩ := chain_foldings_exist hsf (b :: rest)
      htail (fun C hC => hall C (List.mem_cons_of_mem a hC))
    exact ⟨f :: fs_tail, Or.inl (by
      cases htail_prop with
      | inl h => simp [List.length_cons] at h ⊢; omega
      | inr h => simp [List.length_cons] at h)⟩


-- created on 2026-10-24
