import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.SimpleGraph.CaroWei


/--
[caroWeiTest_degree_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CaroWei.lean)
-/
@[path]
lemma caroWeiTest_degree_bot
  {v : Fin 3} :
-- imply
  (⊥ : SimpleGraph (Fin 3)).degree v = 0 := by
-- proof
  change ((⊥ : SimpleGraph (Fin 3)).neighborFinset v).card = 0
  rw [SimpleGraph.neighborFinset_bot]
  simp

/--
[caroWeiTest_degree_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CaroWei.lean)
-/
@[path]
lemma caroWeiTest_degree_top
  {v : Fin 4} :
-- imply
  (⊤ : SimpleGraph (Fin 4)).degree v = 3 := by
-- proof
  change ((⊤ : SimpleGraph (Fin 4)).neighborFinset v).card = 3
  rw [SimpleGraph.neighborFinset_top, Finset.card_compl, Finset.card_singleton,
    Fintype.card_fin]

/--
[caroWeiTest_sum_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CaroWei.lean)
-/
@[path]
lemma caroWeiTest_sum_bot
-- imply
  ∑ v : Fin 3, (1 : ℝ) / ((⊥ : SimpleGraph (Fin 3)).degree v + 1) = 3 := by
-- proof
  have hterm : ∀ v : Fin 3,
    (1 : ℝ) / ((⊥ : SimpleGraph (Fin 3)).degree v + 1) = 1 := by
    intro v
    rw [caroWeiTest_degree_bot v]
    norm_num
  rw [Fin.sum_univ_three]
  simp only [hterm]
  norm_num

/--
[caroWeiTest_sum_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CaroWei.lean)
-/
@[path]
lemma caroWeiTest_sum_top
-- imply
  ∑ v : Fin 4, (1 : ℝ) / ((⊤ : SimpleGraph (Fin 4)).degree v + 1) = 1 := by
-- proof
  have hterm : ∀ v : Fin 4,
    (1 : ℝ) / ((⊤ : SimpleGraph (Fin 4)).degree v + 1) = 1 / 4 := by
    intro v
    rw [caroWeiTest_degree_top v]
    norm_num
  rw [Fin.sum_univ_four]
  simp only [hterm]
  norm_num

/--
[caroWeiTest_sum_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CaroWei.lean)
-/
@[path]
lemma caroWeiTest_sum_empty
-- imply
  (∑ v : Fin 0, (1 : ℝ) / ((⊥ : SimpleGraph (Fin 0)).degree v + 1)) = 0 := by
-- proof
  rw [Finset.univ_eq_empty]
  simp


-- created on 2026-10-23
