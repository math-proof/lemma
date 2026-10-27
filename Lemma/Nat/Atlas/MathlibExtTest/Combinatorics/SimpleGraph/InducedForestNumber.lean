import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.InducedForestNumber


/--
[k3_pair_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
private lemma k3_pair_acyclic :
  ((SimpleGraph.completeGraph (Fin 3)).induce
    (↑({0, 1} : Finset (Fin 3)) : Set (Fin 3))).IsAcyclic := by
  rw [SimpleGraph.induce_top]
  apply SimpleGraph.IsAcyclic.of_card_le_two
  have hfin_eq :
    Fintype.card ↥(↑({0, 1} : Finset (Fin 3)) : Set (Fin 3)) = 2 := by
    decide
  have henat_eq :
    ENat.card ↥(↑({0, 1} : Finset (Fin 3)) : Set (Fin 3)) = 2 := by
    rw [ENat.card_eq_coe_fintype_card, hfin_eq]
    simp
  rw [henat_eq]

/--
[k3_univ_not_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
private lemma k3_univ_not_acyclic :
  ¬ ((SimpleGraph.completeGraph (Fin 3)).induce (Set.univ : Set (Fin 3))).IsAcyclic := by
  rw [SimpleGraph.induce_top]
  intro h
  let a : ↥(Set.univ : Set (Fin 3)) := ⟨0, Set.mem_univ _⟩
  let b : ↥(Set.univ : Set (Fin 3)) := ⟨1, Set.mem_univ _⟩
  let c : ↥(Set.univ : Set (Fin 3)) := ⟨2, Set.mem_univ _⟩
  have hab : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Adj a b := by
    decide
  have hac : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Adj a c := by
    decide
  have hcb : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Adj c b := by
    decide
  have hsub :
    Subsingleton
      ((SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b) :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp h) _ _
  let w1 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b :=
    SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil
  let w2 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b :=
    SimpleGraph.Walk.cons hac (SimpleGraph.Walk.cons hcb SimpleGraph.Walk.nil)
  have hsup1 : w1.support = [a, b] := rfl
  have hsup2 : w2.support = [a, c, b] := rfl
  have hne_ab : a ≠ b := by decide
  have hne_ac : a ≠ c := by decide
  have hne_cb : c ≠ b := by decide
  have hw1 : w1.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsup1]
    exact List.nodup_cons.mpr ⟨by simp [hne_ab], List.nodup_singleton _⟩
  have hw2 : w2.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsup2]
    exact List.nodup_cons.mpr ⟨by simp [hne_ac, hne_ab],
      List.nodup_cons.mpr ⟨by simp [hne_cb], List.nodup_singleton _⟩⟩
  let p1 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b := ⟨w1, hw1⟩
  let p2 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b := ⟨w2, hw2⟩
  have heq : p1 = p2 := @Subsingleton.elim _ hsub _ _
  have hlen := congrArg
    (fun p : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b =>
      ((p : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b).length)) heq
  have h1 :
    ((p1 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b).length) = 1 := rfl
  have h2 :
    ((p2 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b).length) = 2 := rfl
  omega


-- created on 2026-10-23
