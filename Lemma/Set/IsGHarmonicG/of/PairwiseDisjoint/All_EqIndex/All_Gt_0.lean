import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GroupTheory.GHarmonic
open scoped Pointwise


/--
[IsGHarmonic.intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
lemma IsGHarmonic.intro
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
  {U : Fin n → Subgroup G}
  {g : Fin n → G}
-- given
  (hpos : ∀ i, 0 < a i)
  (hidx : ∀ i, (U i).index = a i)
  (hdisj : Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G))) :
-- imply
  IsGHarmonic G a :=
-- proof
  ⟨hpos, U, g, hidx, hdisj⟩

/--
[IsGHarmonic.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
lemma IsGHarmonic.pos
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsGHarmonic G a) :
-- imply
  0 < a i :=
-- proof
  h.1 i

/--
[IsGHarmonic.witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
lemma IsGHarmonic.witnesses
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsGHarmonic G a) :
-- imply
  ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
    (∀ i, (U i).index = a i) ∧
    Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) :=
-- proof
  h.2

/--
[isGHarmonic_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
lemma isGHarmonic_iff
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ} :
-- imply
  IsGHarmonic G a ↔
    (∀ i, 0 < a i) ∧
    ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
    (∀ i, (U i).index = a i) ∧
    Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) :=
-- proof
  Iff.rfl

/--
[isGHarmonic_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
lemma isGHarmonic_empty
  [Group G] :
-- imply
  IsGHarmonic G (n := by
-- proof
  refine ⟨fun i => Fin.elim0 i, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, ?_⟩
  intro i _ j _ hij
  exact (hij (Subsingleton.elim i j)).elim

/--
[isGHarmonic_singleton_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
lemma isGHarmonic_singleton_one
  [Group G] :
-- imply
  IsGHarmonic G (n := by
-- proof
  refine ⟨fun _ => Nat.zero_lt_one, fun _ => ⊤, fun _ => 1, fun i => ?_, ?_⟩
  · exact Subgroup.index_top
  · intro i _ j _ hij
    exact (hij (Subsingleton.elim i j)).elim

/--
[not_isGHarmonic_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
lemma not_isGHarmonic_of_zero
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h0 : a i = 0) :
-- imply
  ¬ IsGHarmonic G a := by
-- proof
  intro h
  have hp := h.pos i
  rw [h0] at hp
  exact Nat.lt_irrefl 0 hp


-- created on 2026-10-20
-- updated on 2026-10-26
