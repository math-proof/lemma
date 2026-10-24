import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SelfGeneratingSet
open MetaMathlibExt
open SelfGeneratingSet


namespace MetaMathlibExt.SelfGeneratingSet

/--
[fixedPoint_isSG](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma fixedPoint_isSG
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hC : FixedPoint F seed C) :
-- imply
  SG F seed C := by
-- proof
  constructor
  · exact (hC seed).mpr (Or.inl rfl)
  · intro f hf x hx
    exact (hC (f x)).mpr (Or.inr ⟨f, hf, x, hx, rfl⟩)

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[generated_isSG](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma generated_isSG
  {F : Finset (Nat → Nat)}
  {seed : Nat} :
-- imply
  SG F seed (GeneratedSet F seed) := by
-- proof
  constructor
  · exact Gen.seed_mem
  · intro f hf x hx
    exact Gen.step x hx f hf

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[generated_le_of_sg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma generated_le_of_sg
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {G : Set Nat}
-- given
  (hG : SG F seed G) :
-- imply
  GeneratedSet F seed ⊆ G := by
-- proof
  intro y hy
  have hgen : Gen F seed y := hy
  clear hy
  induction hgen with
  | seed_mem => exact hG.1
  | step w _ f hf ih => exact hG.2 f hf w ih

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[generated_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma generated_fixedPoint
  {F : Finset (Nat → Nat)}
  {seed : Nat} :
-- imply
  FixedPoint F seed (GeneratedSet F seed) := by
-- proof
  intro y
  constructor
  · intro hy
    have hgen : Gen F seed y := hy
    cases hgen with
    | seed_mem => exact Or.inl rfl
    | step w hw f hf => exact Or.inr ⟨f, hf, w, hw, rfl⟩
  · intro hy
    cases hy with
    | inl heq =>
      subst heq
      exact Gen.seed_mem
    | inr h =>
      obtain ⟨f, hf, x, hx, heq⟩ := h
      have hxg : Gen F seed x := hx
      subst heq
      exact Gen.step x hxg f hf

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[fixedPoint_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma fixedPoint_eq_generated
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hg : StrictGrowth F)
  (hC : FixedPoint F seed C) :
-- imply
  C = GeneratedSet F seed := by
-- proof
  have hSG : SG F seed C := fixedPoint_isSG hC
  have key : ∀ n, n ∈ C → Gen F seed n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hn
      have hor : n = seed ∨ ∃ f ∈ F, ∃ x ∈ C, f x = n := (hC n).mp hn
      cases hor with
      | inl heq =>
        subst heq
        exact Gen.seed_mem
      | inr h =>
        obtain ⟨f, hf, x, hx, heq⟩ := h
        have hlt : x < f x := hg f hf x
        have hlt' : x < n := heq ▸ hlt
        have ihx : Gen F seed x := ihn x hlt' hx
        rw [← heq]
        exact Gen.step x ihx f hf
  apply Set.ext
  intro y
  constructor
  · intro hy
    exact key y hy
  · intro hy
    exact generated_le_of_sg hSG hy

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[generated_eq_sInter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma generated_eq_sInter
  {F : Finset (Nat → Nat)}
  {seed : Nat} :
-- imply
  GeneratedSet F seed = Set.sInter {G | SG F seed G} := by
-- proof
  apply Set.ext
  intro y
  constructor
  · intro hy
    change ∀ G ∈ {G | SG F seed G}, y ∈ G
    intro G hG
    have hGs : SG F seed G := hG
    exact generated_le_of_sg hGs hy
  · intro hy
    have hgenSG : SG F seed (GeneratedSet F seed) := generated_isSG
    have hmem : GeneratedSet F seed ∈ {G | SG F seed G} := hgenSG
    have hy' : ∀ G ∈ {G | SG F seed G}, y ∈ G := hy
    exact hy' _ hmem

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[fixedPoint_eq_sInter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma fixedPoint_eq_sInter
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hg : StrictGrowth F)
  (hC : FixedPoint F seed C) :
-- imply
  C = Set.sInter {G | SG F seed G} := by
-- proof
  rw [fixedPoint_eq_generated hg hC, generated_eq_sInter]

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[fixedPoint_isLeast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma fixedPoint_isLeast
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hg : StrictGrowth F)
  (hC : FixedPoint F seed C) :
-- imply
  SG F seed C ∧ ∀ G, SG F seed G → C ⊆ G := by
-- proof
  constructor
  · exact fixedPoint_isSG hC
  · intro G hG
    rw [fixedPoint_eq_generated hg hC]
    exact generated_le_of_sg hG

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[isLeast_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma isLeast_eq_generated
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hC : SG F seed C)
  (hle : ∀ G, SG F seed G → C ⊆ G) :
-- imply
  C = GeneratedSet F seed := by
-- proof
  apply Set.ext
  intro y
  constructor
  · intro hy
    exact hle _ generated_isSG hy
  · intro hy
    exact generated_le_of_sg hC hy

end MetaMathlibExt.SelfGeneratingSet

namespace MetaMathlibExt.SelfGeneratingSet

/--
[fixedPoint_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
lemma fixedPoint_unique
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C1 C2 : Set Nat}
-- given
  (hg : StrictGrowth F)
  (h0 : FixedPoint F seed C1)
  (h1 : FixedPoint F seed C2) :
-- imply
  C1 = C2 := by
-- proof
  rw [fixedPoint_eq_generated hg h1, fixedPoint_eq_generated hg h2]

end MetaMathlibExt.SelfGeneratingSet


-- created on 2026-10-20
-- updated on 2026-10-23
