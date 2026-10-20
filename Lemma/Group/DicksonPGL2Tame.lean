import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.DicksonPGL2Tame
open scoped BigOperators
open MetaMathlibExt
open Dickson


/--
[classification_tame](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma classification_tame_eq
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
  {G : Subgroup (PGL p)} [Finite G]
-- given
  (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
  (hG_nontrivial : Nontrivial G) :
-- imply
  (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) := by
-- proof
  apply MetaMathlibExt.Dickson.classification_tame p G hG_tame hG_nontrivial


-- created on 2026-10-20
