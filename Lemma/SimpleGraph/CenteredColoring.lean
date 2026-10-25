import Mathlib
import sympy.Basic
import Def.Combinatorics.SimpleGraph.CenteredColoring
open SimpleGraph


namespace SimpleGraph

/--
[isPhiCenter_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
lemma isPhiCenter_singleton
  {G : SimpleGraph V}
  {φ : G.Coloring C}
  {v : V} :
-- imply
  IsPhiCenter φ {v} v :=
-- proof
  ⟨Set.mem_singleton v, fun _ hw _ => Set.mem_singleton_iff.mp hw⟩

end SimpleGraph

namespace SimpleGraph

/--
[isCentered_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
lemma isCentered_of_injective
  {G : SimpleGraph V}
  {φ : G.Coloring C}
-- given
  (hinj : Function.Injective ⇑φ) :
-- imply
  IsCentered φ := by
-- proof
  intro s hs
  have hne : s.Nonempty := Set.nonempty_coe_sort.mp hs.nonempty
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv, fun w _ heq => hinj heq⟩

end SimpleGraph

namespace SimpleGraph

/--
[selfColoring_isCentered](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
lemma selfColoring_isCentered
  {G : SimpleGraph V} :
-- imply
  IsCentered (SimpleGraph.selfColoring G) :=
-- proof
  isCentered_of_injective (SimpleGraph.selfColoring G) fun _ _ h => h

end SimpleGraph

/--
[isPhiCenter_iff_existsUnique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
lemma isPhiCenter_iff_existsUnique
  {G : SimpleGraph V}
  {φ : G.Coloring C}
  {s : Set V}
  {v : V} :
-- imply
  IsPhiCenter φ s v ↔ v ∈ s ∧ ∃! u, u ∈ s ∧ φ u = φ v := by
-- proof
  constructor
  · rintro ⟨hmem, huniq⟩
    refine ⟨hmem, v, ⟨hmem, rfl⟩, ?_⟩
    rintro w ⟨hwmem, hweq⟩
    exact huniq w hwmem hweq
  · rintro ⟨hmem, u₀, ⟨_, _⟩, huniq⟩
    refine ⟨hmem, fun w hwmem hweq => ?_⟩
    have hw : w = u₀ := huniq w ⟨hwmem, hweq⟩
    have hv : v = u₀ := huniq v ⟨hmem, rfl⟩
    exact hw.trans hv.symm



-- created on 2026-10-20
-- updated on 2026-10-23
