import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits

/--
[CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq.lean)
-/
@[main]
private lemma main
  {C : Type w} [Category.{v} C]
  {X X' S T : C}
  {f : X ⟶ S}
  {f' : X' ⟶ S}
  {t : T ⟶ S} [HasPullback f t] [HasPullback f' t]
  {π : X' ⟶ X}
-- given
  (hπ : π ≫ f = f') :
-- imply
  IsPullback (pullback.fst f' t)
      (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp]))
      π (pullback.fst f t) := by
-- proof
  have big : IsPullback (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ])
      (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd f t) (pullback.fst f' t) t (π ≫ f) := by
    rw [pullback.lift_snd, Category.comp_id, hπ]
    exact (IsPullback.of_hasPullback f' t).flip
  exact (IsPullback.of_right big (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f t).flip).flip


-- created on 2026-10-05
