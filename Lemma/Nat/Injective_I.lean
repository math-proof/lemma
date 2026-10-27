import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Nat.EqEquivMapDomain_EquivMapDomainSymm
open Nat


/--
[rothLastIndex_left_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  (a : ℕ) :
-- imply
  Function.Injective
    (fun i : Finsupp (Fin n) ℕ ↦
      (Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)) := by
-- proof
  intro i j hij
  have hcast :
    ∀ (i : Finsupp (Fin n) ℕ) (a : ℕ) (h : Fin n),
      ((Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)) h.castSucc =
        i h := by
    intro i a h
    have heq :
      (Finsupp.equivCongrLeft finSuccEquivLast)
        ((Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)) =
        Finsupp.optionElim a i := by
      simpa [Finsupp.equivCongrLeft_apply] using
        EqEquivMapDomain_EquivMapDomainSymm finSuccEquivLast (Finsupp.optionElim a i)
    have := congrArg (fun d : Finsupp (Option (Fin n)) ℕ ↦ d (some h)) heq
    simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]
  ext h
  have := congrArg (fun d : Finsupp (Fin (n + 1)) ℕ ↦ d h.castSucc) hij
  simpa [hcast] using this


-- created on 2026-10-21
