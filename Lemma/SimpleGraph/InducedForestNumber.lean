import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.InducedForestNumber
open SimpleGraph


namespace SimpleGraph

/--
[card_le_inducedForestNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
lemma card_le_inducedForestNumber
  [Fintype V]
  {G : SimpleGraph V}
  {s : Finset V}
-- given
  (h : (G.induce (↑s : Set V)).IsAcyclic) :
-- imply
  s.card ≤ G.inducedForestNumber := by
-- proof
  classical
  unfold inducedForestNumber
  have hmem : s ∈ Finset.univ.powerset (α := V) := by simp
  have hif : (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) = s.card :=
    ite_eq_left h
  calc s.card
    = (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) := hif.symm
    _ ≤ Finset.sup (Finset.univ.powerset (α := V))
      (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0) :=
      Finset.le_sup (s := Finset.univ.powerset (α := V))
        (f := fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0)
        hmem

end SimpleGraph

namespace SimpleGraph

/--
[inducedForestNumber_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
lemma inducedForestNumber_le_card
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  G.inducedForestNumber ≤ Fintype.card V := by
-- proof
  classical
  unfold inducedForestNumber
  apply Finset.sup_le
  intro s hs
  by_cases h : (G.induce (↑s : Set V)).IsAcyclic
  · simp only [ite_eq_left h]
    exact Finset.card_le_univ s
  · simp only [ite_eq_right h]
    exact Nat.zero_le _

end SimpleGraph

namespace SimpleGraph

/--
[exists_isAcyclic_card_eq_inducedForestNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
lemma exists_isAcyclic_card_eq_inducedForestNumber
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  ∃ s : Finset V, (G.induce (↑s : Set V)).IsAcyclic ∧ s.card = G.inducedForestNumber := by
-- proof
  classical
  unfold inducedForestNumber
  have hne : (Finset.univ.powerset (α := V)).Nonempty := ⟨∅, by simp⟩
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup (Finset.univ.powerset (α := V)) hne
    (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0)
  by_cases h : (G.induce (↑s : Set V)).IsAcyclic
  · refine ⟨s, h, ?_⟩
    have hif : (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) = s.card :=
      ite_eq_left h
    exact (heq.trans hif).symm
  · have hif : (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) = 0 :=
    ite_eq_right h
    have hsup : (0 : Nat) = Finset.sup (Finset.univ.powerset (α := V))
      (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0) :=
      (heq.trans hif).symm
    have hsub : Subsingleton ↥(((∅ : Finset V) : Set V)) :=
      ⟨fun a _ => False.elim (by simpa using a.property)⟩
    have hempty : (G.induce (((∅ : Finset V) : Set V))).IsAcyclic :=
      @SimpleGraph.IsAcyclic.of_subsingleton _ hsub _
    refine ⟨∅, hempty, ?_⟩
    calc (∅ : Finset V).card = 0 := by simp
      _ = Finset.sup (Finset.univ.powerset (α := V))
        (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0) := hsup

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
