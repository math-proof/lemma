/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Lemma.Set.SocialChoice.Arrow
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push
import Def.GameTheory.SocialChoice.Arrow.Part3
import Def.GameTheory.SocialChoice.GibbardSatterthwaite


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

-- Helper lemmas (all with explicit binders; no `variable`).
-- Step 1: monotonicity (Maskin) from strategy-proofness.

/-- Asymmetry of a strict total order. -/
theorem sto_asymm {Alt : Type*} (o : StrictTotalOrder Alt) {a b : Alt}
    (h : o.lt a b) : ¬ o.lt b a :=
  fun h2 => o.irrefl a (o.trans h h2)

/-- Single-voter deviation the other way is also unilateral. -/
theorem diffAtMostAt_update_left {Alt Voter : Type*} [DecidableEq Voter]
    (R : Profile Alt Voter) (i : Voter) (v : StrictTotalOrder Alt) :
    DiffAtMostAt (Function.update R i v) R i :=
  fun _j hj => Function.update_of_ne hj v R

/-- Single-voter deviation is unilateral. -/
theorem diffAtMostAt_update_right {Alt Voter : Type*} [DecidableEq Voter]
    (R : Profile Alt Voter) (i : Voter) (v : StrictTotalOrder Alt) :
    DiffAtMostAt R (Function.update R i v) i :=
  fun _j hj => (Function.update_of_ne hj v R).symm

/-- One-voter monotonicity: improving the winner's position for one voter
does not change the outcome. Proved by applying strategy-proofness in both
directions. -/
theorem mono_one {Alt Voter : Type*} [DecidableEq Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (R : Profile Alt Voter) (i : Voter) (v : StrictTotalOrder Alt)
    (hpres : ∀ b, (R i).lt (F R) b → v.lt (F R) b) :
    F (Function.update R i v) = F R := by
  by_contra hne
  have hSP1 : ¬ (R i).lt (F (Function.update R i v)) (F R) :=
    hSP R i (Function.update R i v) (diffAtMostAt_update_right R i v)
  have hSP2 : ¬ (Function.update R i v i).lt (F R) (F (Function.update R i v)) :=
    hSP (Function.update R i v) i R (diffAtMostAt_update_left R i v)
  rw [Function.update_self] at hSP2
  have hne' : F (Function.update R i v) ≠ F R := hne
  rcases (R i).total hne' with h1 | h1
  · exact hSP1 h1
  · exact hSP2 (hpres _ h1)

/-- Multi-voter monotonicity: if every voter's new order preserves every
comparison won by the old winner, the outcome is unchanged. Proved by
changing voters one at a time (`Finset.induction`). -/
theorem mono_many {Alt Voter : Type*} [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (R S : Profile Alt Voter)
    (hpres : ∀ (i : Voter) (b : Alt), (R i).lt (F R) b → (S i).lt (F R) b) :
    F S = F R := by
  classical
  have := Fintype.ofFinite Voter
  let x : Alt := F R
  let M : Finset Voter → Profile Alt Voter := fun T i => if i ∈ T then S i else R i
  have hM_empty : M ∅ = R := by
    funext i
    simp [M]
  have hM_univ : M Finset.univ = S := by
    funext i
    simp [M]
  have hM_insert : ∀ (T : Finset Voter) (k : Voter), k ∉ T →
      M (insert k T) = Function.update (M T) k (S k) := by
    intro T k hk
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp [M]
    · rw [Function.update_of_ne hjk]
      simp only [M]
      have hmem : (j ∈ insert k T) = (j ∈ T) := by
        simp [Finset.mem_insert, hjk]
      simp only [hmem]
  have key : ∀ T : Finset Voter, T ⊆ Finset.univ → F (M T) = x := by
    refine Finset.induction ?_ ?_
    · intro _
      rw [hM_empty]
    · intro k T hk ih hsub
      have hMT : F (M T) = x :=
        ih (Finset.Subset.trans (Finset.subset_insert k T) hsub)
      have hUpd : M (insert k T) = Function.update (M T) k (S k) :=
        hM_insert T k hk
      have hMk : M T k = R k := by simp [M, hk]
      have hpres' : ∀ b, (M T k).lt (F (M T)) b → (S k).lt (F (M T)) b := by
        intro b hb
        rw [hMT] at hb ⊢
        rw [hMk] at hb
        exact hpres k b hb
      have hmono := mono_one F hSP (M T) k (S k) hpres'
      rw [hUpd, hmono, hMT]
  have := key Finset.univ (Finset.subset_univ _)
  rw [hM_univ] at this
  exact this

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
