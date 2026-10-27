import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose.Part3
open Finset StatMech StatMech.Walls StatMech.Walls.Reimer


/--
[rb3_toB_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_toB_apply_eq
  {n : ℕ}
  {S : Finset (Fin n)}
  {i : Fin n} :
-- imply
  rb3_toB S i = decide (i ∈ S) := by
-- proof
  apply StatMech.Walls.Reimer.rb3_toB_apply S i

/--
[rb3_mem_ofB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_mem_ofB_eq
  {n : ℕ}
  {x : rbt_Q n}
  {i : Fin n} :
-- imply
  i ∈ rb3_ofB x ↔ x i = true := by
-- proof
  apply StatMech.Walls.Reimer.rb3_mem_ofB x i

/--
[rb3_ofB_toB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_ofB_toB_eq
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  rb3_ofB (rb3_toB S) = S := by
-- proof
  apply StatMech.Walls.Reimer.rb3_ofB_toB S

/--
[rb3_toB_ofB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_toB_ofB_eq
  {n : ℕ}
  {x : rbt_Q n} :
-- imply
  rb3_toB (rb3_ofB x) = x := by
-- proof
  apply StatMech.Walls.Reimer.rb3_toB_ofB x

/--
[rb3_toB_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_toB_injective_eq
  {n : ℕ} :
-- imply
  Function.Injective (rb3_toB (n := n)) := by
-- proof
  apply StatMech.Walls.Reimer.rb3_toB_injective

/--
[rb3_toB_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_toB_compl_eq
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  rbt_antipode (rb3_toB S) = rb3_toB Sᶜ := by
-- proof
  apply StatMech.Walls.Reimer.rb3_toB_compl S

/--
[rb3_inter_eq_iff_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_inter_eq_iff_agree_eq
  {n : ℕ}
  {K S T : Finset (Fin n)} :
-- imply
  T ∩ K = S ∩ K ↔ ∀ i ∈ K, rb3_toB T i = rb3_toB S i := by
-- proof
  apply StatMech.Walls.Reimer.rb3_inter_eq_iff_agree K S T

/--
[rb3_witK_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_witK_spec_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  (∀ T : Finset (Fin n), T ∩ (rb3_witK 𝒜 ℬ S) = S ∩ (rb3_witK 𝒜 ℬ S) → T ∈ 𝒜) ∧ (∀ T : Finset (Fin n), T ∩ (rb3_witK 𝒜 ℬ S)ᶜ = S ∩ (rb3_witK 𝒜 ℬ S)ᶜ → T ∈ ℬ) := by
-- proof
  apply StatMech.Walls.Reimer.rb3_witK_spec 𝒜 ℬ hS

/--
[rb3_body_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_body_apply_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
  {i : Fin n} :
-- imply
  rb3_body 𝒜 ℬ (rb3_toB S) i = (if i ∈ rb3_witK 𝒜 ℬ S then rb3_toB S i else !(rb3_toB S i)) := by
-- proof
  apply StatMech.Walls.Reimer.rb3_body_apply 𝒜 ℬ S i

/--
[rb3_inRed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_inRed_iff_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
  {x : rbt_Q n} :
-- imply
  rbt_inRed (rb3_body 𝒜 ℬ (rb3_toB S)) (rb3_toB S) x ↔ (rb3_ofB x) ∩ (rb3_witK 𝒜 ℬ S) = S ∩ (rb3_witK 𝒜 ℬ S) := by
-- proof
  apply StatMech.Walls.Reimer.rb3_inRed_iff 𝒜 ℬ S x

/--
[rb3_inYellow_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_inYellow_iff_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
  {x : rbt_Q n} :
-- imply
  rbt_inYellow (rb3_body 𝒜 ℬ (rb3_toB S)) (rb3_toB S) x ↔ (rb3_ofB x)ᶜ ∩ (rb3_witK 𝒜 ℬ S)ᶜ = S ∩ (rb3_witK 𝒜 ℬ S)ᶜ := by
-- proof
  apply StatMech.Walls.Reimer.rb3_inYellow_iff 𝒜 ℬ S x

/--
[rb3_red_mem_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_red_mem_A_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {x : rbt_Q n}
-- given
  (hx : x ∈ rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
-- imply
  rb3_ofB x ∈ 𝒜 := by
-- proof
  apply StatMech.Walls.Reimer.rb3_red_mem_A 𝒜 ℬ hx

/--
[rb3_yellow_mem_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_yellow_mem_B_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {x : rbt_Q n}
-- given
  (hx : x ∈ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
-- imply
  (rb3_ofB x)ᶜ ∈ ℬ := by
-- proof
  apply StatMech.Walls.Reimer.rb3_yellow_mem_B 𝒜 ℬ hx

/--
[rb3_redYellow_ofB_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_redYellow_ofB_mem_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {x : rbt_Q n}
-- given
  (hx : x ∈ rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB) ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
-- imply
  rb3_ofB x ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.Reimer.rb3_redYellow_ofB_mem_reflInter 𝒜 ℬ hx

/--
[rb3_card_redYellow_le_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_card_redYellow_le_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB) ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)).card ≤ (rc10_reflInter 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.Reimer.rb3_card_redYellow_le_reflInter 𝒜 ℬ

/--
[rb3_card_tips](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_card_tips_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  ((rc20_famCylBox 𝒜 ℬ).image rb3_toB).card = (rc20_famCylBox 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.Reimer.rb3_card_tips 𝒜 ℬ

/--
[rb3_famCylBox_le_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_famCylBox_le_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.Reimer.rb3_famCylBox_le_reflInter 𝒜 ℬ

/--
[rb3_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_famCylBoxResidue_eq :
-- imply
  StatMech.Walls.rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.Reimer.rb3_famCylBoxResidue

/--
[rb3_reimerWprobCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_reimerWprobCore_eq :
-- imply
  StatMech.ReimerWprobCore := by
-- proof
  apply StatMech.Walls.Reimer.rb3_reimerWprobCore

/--
[rb3_thm_reimer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean)
-/
@[path]
private lemma rb3_thm_reimer_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (StatMech.ConfigSpace E)}
-- given
  (hp : p ≤ 1) :
-- imply
  (StatMech.bernoulliProductMeasure (E := E) p hp).real (StatMech.disjointOccurrence A B) ≤ (StatMech.bernoulliProductMeasure (E := E) p hp).real A * (StatMech.bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.Reimer.rb3_thm_reimer hp A B


-- created on 2026-10-23
