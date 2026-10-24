/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/InducedForestNumber.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.InducedForestNumber
import Lemma.SimpleGraph.InducedForestNumber


#check @SimpleGraph.inducedForestNumber
#check @SimpleGraph.card_le_inducedForestNumber
#check @SimpleGraph.inducedForestNumber_le_card
#check @SimpleGraph.exists_isAcyclic_card_eq_inducedForestNumber

example (G : SimpleGraph (Fin 0)) : G.inducedForestNumber = 0 := by
  have hle : G.inducedForestNumber ≤ Fintype.card (Fin 0) :=
    SimpleGraph.inducedForestNumber_le_card G
  simp at hle
  omega

example : (⊥ : SimpleGraph (Fin 3)).inducedForestNumber = 3 := by
  classical
  have hbot : (⊥ : SimpleGraph (Fin 3)).IsAcyclic := by
    simp
  have huniv : ((⊥ : SimpleGraph (Fin 3)).induce
      ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))).IsAcyclic :=
    hbot.induce ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))
  have hge : (Finset.univ : Finset (Fin 3)).card ≤
      (⊥ : SimpleGraph (Fin 3)).inducedForestNumber :=
    SimpleGraph.card_le_inducedForestNumber _ _ huniv
  have hle : (⊥ : SimpleGraph (Fin 3)).inducedForestNumber ≤ Fintype.card (Fin 3) :=
    SimpleGraph.inducedForestNumber_le_card _
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have hcardu : (Finset.univ : Finset (Fin 3)).card = 3 := by simp [hcard]
  omega

example : (SimpleGraph.completeGraph (Fin 3)).inducedForestNumber = 2 := by
  classical
  have h2 : ((SimpleGraph.completeGraph (Fin 3)).induce
      (↑({0, 1} : Finset (Fin 3)) : Set (Fin 3))).IsAcyclic :=
    k3_pair_acyclic
  have hnot : ¬ ((SimpleGraph.completeGraph (Fin 3)).induce
      (Set.univ : Set (Fin 3))).IsAcyclic :=
    k3_univ_not_acyclic
  have hcard01 : ({0, 1} : Finset (Fin 3)).card = 2 := by
    decide
  have hge : 2 ≤ (SimpleGraph.completeGraph (Fin 3)).inducedForestNumber := by
    have hle := SimpleGraph.card_le_inducedForestNumber
      (SimpleGraph.completeGraph (Fin 3)) ({0, 1} : Finset (Fin 3)) h2
    omega
  have hle2 : (SimpleGraph.completeGraph (Fin 3)).inducedForestNumber ≤ 2 := by
    classical
    unfold SimpleGraph.inducedForestNumber
    apply Finset.sup_le
    intro s _
    by_cases h : ((SimpleGraph.completeGraph (Fin 3)).induce (↑s : Set (Fin 3))).IsAcyclic
    · simp only [ite_eq_left h]
      have hcard3 : s.card ≤ 3 := by
        calc s.card ≤ Fintype.card (Fin 3) := Finset.card_le_univ s
          _ = 3 := Fintype.card_fin 3
      by_cases h3 : s.card = 3
      · have hsuniv : s = Finset.univ :=
          Finset.eq_univ_of_card s (h3.trans (Fintype.card_fin 3).symm)
        have hset : (↑s : Set (Fin 3)) = Set.univ := by
          rw [hsuniv, Finset.coe_univ]
        exact absurd (hset ▸ h) hnot
      · omega
    · simp only [ite_eq_right h]
      exact Nat.zero_le _
  omega
