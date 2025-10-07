import Lemma.Set.Eq.of.All_Imp.All_Imp
import Lemma.Set.In_Cup.is.Any_In
import Lemma.Set.In_Ite.is.OrAndS
import Lemma.Bool.Any_Or.is.OrAnyS
import Lemma.Set.In_Union.is.OrInS
import Lemma.Bool.Any_And.is.AnyAnd
import Lemma.Set.In_Inter.is.In.In
import Lemma.Set.In_SDiff.is.In.NotIn
import Lemma.Set.Inter
open Set Bool


@[main, comm]
private lemma main
-- given
  (A B : Set α)
  (f g : α → Set β)
  (h : (x : α) → Decidable (x ∈ B)) :
-- imply
  (⋃ x ∈ A, if x ∈ B then
    f x
  else
    g x) = (⋃ x ∈ A ∩ B, f x) ∪ ⋃ x ∈ A \ B, g x := by
-- proof
  apply Eq.of.All_Imp.All_Imp <;>
    intro y h
  ·
    obtain ⟨x, h_in, h⟩ := Any_In.of.In_Cup.set h
    have h := OrAndS.of.In_Ite h
    obtain h_f | h_g := h
    ·
      left
      aesop
    ·
      right
      aesop
  ·
    simp [In_Ite.is.OrAndS]
    apply Any_Or.of.OrAnyS.set
    simp [Any_And.is.AnyAnd.comm]
    have h := OrInS.of.In_Union h
    obtain h | h := h <;>
      simp_all


-- created on 2025-08-01
-- updated on 2025-08-02
