import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Nat.EqEquivMapDomain_EquivMapDomainSymm
open Nat


/--
[rothLastIndex_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  (i j : Finsupp (Fin n) ℕ)
  (a b : ℕ) :
-- imply
  (Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim (a + b) (i + j)) =
    (Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i) +
      (Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim b j) := by
-- proof
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
  have hlast :
    ∀ (i : Finsupp (Fin n) ℕ) (a : ℕ),
      ((Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)) (Fin.last n) =
        a := by
    intro i a
    have heq :
      (Finsupp.equivCongrLeft finSuccEquivLast)
        ((Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)) =
        Finsupp.optionElim a i := by
      simpa [Finsupp.equivCongrLeft_apply] using
        EqEquivMapDomain_EquivMapDomainSymm finSuccEquivLast (Finsupp.optionElim a i)
    have := congrArg (fun d : Finsupp (Option (Fin n)) ℕ ↦ d none) heq
    simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]
  ext h
  refine Fin.lastCases ?_ (fun t ↦ ?_) h
  ·
    rw [hlast (i + j) (a + b)]
    conv_rhs => rw [Finsupp.add_apply]
    rw [hlast i a, hlast j b]
  ·
    rw [hcast (i + j) (a + b) t]
    conv_rhs => rw [Finsupp.add_apply]
    rw [hcast i a t, hcast j b t]
    rw [Finsupp.add_apply]


-- created on 2026-10-21
