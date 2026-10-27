import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.GeneralizedExtremal
open SimpleGraph


variable {α β : Type*} [Fintype α]
variable (T : SimpleGraph α) (H : SimpleGraph β)
variable (n : ℕ)
variable (G : SimpleGraph (Fin n)) (hG : H.Free G)
variable (m : ℕ)
/--
[concrete_K3_free_in_K2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
private lemma concrete_K3_free_in_K2 :
  (completeGraph (Fin 3)).Free (completeGraph (Fin 2)) := by
  intro h
  obtain ⟨c⟩ := h
  have hle : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_embedding c.toEmbedding
  exact absurd hle (by decide)

variable {α β : Type*} [Fintype α]
variable (T : SimpleGraph α) (H : SimpleGraph β)
variable (n : ℕ)
variable (G : SimpleGraph (Fin n)) (hG : H.Free G)
variable (m : ℕ)
/--
[concrete_K3_free_all_Fin2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
private lemma concrete_K3_free_all_Fin2 (G : SimpleGraph (Fin 2)) :
  (completeGraph (Fin 3)).Free G := by
  intro h
  obtain ⟨c⟩ := h
  have hle : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_embedding c.toEmbedding
  exact absurd hle (by decide)

variable {α β : Type*} [Fintype α]
variable (T : SimpleGraph α) (H : SimpleGraph β)
variable (n : ℕ)
variable (G : SimpleGraph (Fin n)) (hG : H.Free G)
variable (m : ℕ)
/--
[concrete_copyCount_K3_on_Fin2_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
private lemma concrete_copyCount_K3_on_Fin2_eq_zero (G : SimpleGraph (Fin 2)) :
  G.copyCount (completeGraph (Fin 3)) = 0 :=
  SimpleGraph.copyCount_eq_zero.mpr (concrete_K3_free_all_Fin2 G)


-- created on 2026-10-23
