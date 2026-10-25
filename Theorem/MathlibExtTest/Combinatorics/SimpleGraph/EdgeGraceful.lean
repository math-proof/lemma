/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Def.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful


namespace EdgeGracefulTest

/-- Empty graph is graceful via the canonical empty bijections. -/
example : (⊥ : SimpleGraph Empty).IsEdgeGraceful := by
  classical
  have hE : (⊥ : SimpleGraph Empty).edgeSet = ∅ := SimpleGraph.edgeSet_bot
  have : Fintype (⊥ : SimpleGraph Empty).edgeSet := Fintype.ofFinite _
  have hEmpty : IsEmpty (⊥ : SimpleGraph Empty).edgeSet :=
    Set.isEmpty_coe_sort.mpr hE
  have hc : Fintype.card (⊥ : SimpleGraph Empty).edgeSet = 0 :=
    Fintype.card_eq_zero_iff.mpr hEmpty
  set eLabel : (⊥ : SimpleGraph Empty).edgeSet ≃ Fin 0 :=
    (Fintype.equivFin _).trans (finCongr hc)
  refine ⟨0, eLabel, ?_⟩
  have hfun : (⊥ : SimpleGraph Empty).inducedResidue 0 eLabel =
      ⇑(Fintype.equivFin Empty) :=
    funext fun v => Empty.elim v
  rw [hfun]
  exact (Fintype.equivFin Empty).bijective

/-- Singleton edgeless graph is graceful. -/
example : (⊥ : SimpleGraph (Fin 1)).IsEdgeGraceful := by
  classical
  have hE : (⊥ : SimpleGraph (Fin 1)).edgeSet = ∅ := SimpleGraph.edgeSet_bot
  have : Fintype (⊥ : SimpleGraph (Fin 1)).edgeSet := Fintype.ofFinite _
  have hEmpty : IsEmpty (⊥ : SimpleGraph (Fin 1)).edgeSet :=
    Set.isEmpty_coe_sort.mpr hE
  have hc : Fintype.card (⊥ : SimpleGraph (Fin 1)).edgeSet = 0 :=
    Fintype.card_eq_zero_iff.mpr hEmpty
  set eLabel : (⊥ : SimpleGraph (Fin 1)).edgeSet ≃ Fin 0 :=
    (Fintype.equivFin _).trans (finCongr hc)
  refine ⟨0, eLabel, ?_⟩
  have hp1 : Fintype.card (Fin 1) = 1 := by simp
  have : Subsingleton (Fin 1) := inferInstance
  have : Subsingleton (Fin (Fintype.card (Fin 1))) := hp1.symm ▸ inferInstance
  constructor
  · intro a b h
    exact Subsingleton.elim a b
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-- `K2` is not edge-graceful: both residues coincide. -/
example : ¬ (⊤ : SimpleGraph (Fin 2)).IsEdgeGraceful := by
  classical
  rintro ⟨q, label, hbij⟩
  have hne : Fintype.card (Fin 2) ≠ 0 := by simp
  have hmem : ∀ k : Fin q,
      (0 : Fin 2) ∈ (label.symm k).val ∧ (1 : Fin 2) ∈ (label.symm k).val :=
    fun k => key2 _ (label.symm k).property
  have hsum : (⊤ : SimpleGraph (Fin 2)).incidentSum q label 0 =
      (⊤ : SimpleGraph (Fin 2)).incidentSum q label 1 := by
    unfold SimpleGraph.incidentSum
    apply Finset.sum_congr rfl
    intro k _
    simp only [(hmem k).1, (hmem k).2]
  have hval : ((⊤ : SimpleGraph (Fin 2)).inducedResidue q label 0).val =
      ((⊤ : SimpleGraph (Fin 2)).inducedResidue q label 1).val := by
    rw [SimpleGraph.inducedResidue_val _ q label 0 hne,
      SimpleGraph.inducedResidue_val _ q label 1 hne, hsum]
  have heq01 : (⊤ : SimpleGraph (Fin 2)).inducedResidue q label 0 =
      (⊤ : SimpleGraph (Fin 2)).inducedResidue q label 1 := Fin.ext hval
  have h01 : (0 : Fin 2) = 1 := hbij.injective heq01
  exact (by decide : (0 : Fin 2) ≠ 1) h01

end EdgeGracefulTest
