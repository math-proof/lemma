/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CaroWei.lean -/


import Mathlib.Algebra.BigOperators.Fin
import Lemma.SimpleGraph.CaroWei
import Mathlib.Tactic.NormNum


example : (3 : ℝ) ≤ (⊥ : SimpleGraph (Fin 3)).indepNum := by
  classical
  have h := SimpleGraph.caroWei_le_indepNum (G := (⊥ : SimpleGraph (Fin 3)))
  rwa [caroWeiTest_sum_bot] at h

example : (1 : ℝ) ≤ (⊤ : SimpleGraph (Fin 4)).indepNum := by
  classical
  have h := SimpleGraph.caroWei_le_indepNum (G := (⊤ : SimpleGraph (Fin 4)))
  rwa [caroWeiTest_sum_top] at h

example : (0 : ℝ) ≤ (⊥ : SimpleGraph (Fin 0)).indepNum := by
  classical
  have h := SimpleGraph.caroWei_le_indepNum (G := (⊥ : SimpleGraph (Fin 0)))
  rwa [caroWeiTest_sum_empty] at h

example : ∃ s : Finset (Fin 3),
    (⊥ : SimpleGraph (Fin 3)).IsIndepSet (s : Set (Fin 3)) ∧ 3 ≤ s.card := by
  classical
  obtain ⟨s, hs, hsum⟩ :=
    SimpleGraph.exists_isIndepSet_caroWei (G := (⊥ : SimpleGraph (Fin 3)))
  rw [caroWeiTest_sum_bot] at hsum
  exact ⟨s, hs, by exact_mod_cast hsum⟩

example : ∃ s : Finset (Fin 4),
    (⊤ : SimpleGraph (Fin 4)).IsIndepSet (s : Set (Fin 4)) ∧ 1 ≤ s.card := by
  classical
  obtain ⟨s, hs, hsum⟩ :=
    SimpleGraph.exists_isIndepSet_caroWei (G := (⊤ : SimpleGraph (Fin 4)))
  rw [caroWeiTest_sum_top] at hsum
  exact ⟨s, hs, by exact_mod_cast hsum⟩

example : ∃ s : Finset (Fin 0),
    (⊥ : SimpleGraph (Fin 0)).IsIndepSet (s : Set (Fin 0)) ∧ 0 ≤ s.card := by
  classical
  obtain ⟨s, hs, hsum⟩ :=
    SimpleGraph.exists_isIndepSet_caroWei (G := (⊥ : SimpleGraph (Fin 0)))
  rw [caroWeiTest_sum_empty] at hsum
  exact ⟨s, hs, by exact_mod_cast hsum⟩

