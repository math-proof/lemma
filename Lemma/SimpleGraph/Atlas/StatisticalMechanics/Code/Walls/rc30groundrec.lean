import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc30groundrec.Part2
open Finset StatMech StatMech.Walls


/--
[rc30_wall_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_wall_base_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc28_famCylBoxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc30_wall_base 𝒜 ℬ

/--
[rc30_wall_of_sameSideReflDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_wall_of_sameSideReflDom_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc30_SameSideReflDom (α := α)) :
-- imply
  ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α), #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc30_wall_of_sameSideReflDom h

/--
[rc30_famCylBoxResidue_of_sameSideReflDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_famCylBoxResidue_of_sameSideReflDom_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : ∀ {β : Type} [Fintype β] [DecidableEq β], rc30_SameSideReflDom (α := β)) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc30_famCylBoxResidue_of_sameSideReflDom h n 𝒜 ℬ

/--
[rc30_sameSideReflDom_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_sameSideReflDom_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (#(rc14_reflE ((univ : Finset (Fin 3)).erase 0) (({∅} : Finset (Finset (Fin 3))).nonMemberSubfamily 0) (({{1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)) + #(rc14_reflE ((univ : Finset (Fin 3)).erase 0) (({∅} : Finset (Finset (Fin 3))).memberSubfamily 0) (({{1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) ≤ #(rc14_reflE ((univ : Finset (Fin 3)).erase 0) (({∅} : Finset (Finset (Fin 3))).nonMemberSubfamily 0) (({{1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) + #(rc14_reflE ((univ : Finset (Fin 3)).erase 0) (({∅} : Finset (Finset (Fin 3))).memberSubfamily 0) (({{1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))) := by
-- proof
  apply StatMech.Walls.rc30_sameSideReflDom_false

/--
[rc30_not_sameSideReflDom_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_not_sameSideReflDom_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc30_SameSideReflDom (α := Fin 3) := by
-- proof
  apply StatMech.Walls.rc30_not_sameSideReflDom_fin3

/--
[rc30_wall_holds_on_overshoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_wall_holds_on_overshoot_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) ≤ #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) := by
-- proof
  apply StatMech.Walls.rc30_wall_holds_on_overshoot

/--
[rc30_wall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_wall_fin2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), #(rc28_famCylBoxE (univ : Finset (Fin 2)) 𝒜 ℬ) ≤ #(rc14_reflE (univ : Finset (Fin 2)) 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc30_wall_fin2

/--
[rc30_flipCandidate_overshoots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_flipCandidate_overshoots_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) < #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) (rc29_flipA 0 ({{1, 2}} : Finset (Finset (Fin 3))))) := by
-- proof
  apply StatMech.Walls.rc30_flipCandidate_overshoots

/--
[rc30_reimer_groundrec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean)
-/
@[path]
private lemma rc30_reimer_groundrec_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset α)), #(rc28_famCylBoxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ)) ∧ (rc30_SameSideReflDom (α := α) → ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α), #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)) ∧ (¬ rc30_SameSideReflDom (α := Fin 3)) ∧ (#(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) ≤ #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}}))) := by
-- proof
  apply StatMech.Walls.rc30_reimer_groundrec


-- created on 2026-10-23
