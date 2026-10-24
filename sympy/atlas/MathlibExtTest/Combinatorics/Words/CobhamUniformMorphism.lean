/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Words/CobhamUniformMorphism.lean -/


import sympy.atlas.Combinatorics.Words.CobhamUniformMorphism
import Lemma.Finset.Words.CobhamUniformMorphism

namespace MetaMathlibExt

example : baseWordValueLSD ([] : List (Fin 2)) = 0 := rfl

-- Least significant digit first: `[1, 0, 1, 1]` in base 2 is `1 + 4 + 8`.
example : baseWordValueLSD ([1, 0, 1, 1] : List (Fin 2)) = 13 := rfl

-- Trailing high-order zeros do not change the value.
example :
    baseWordValueLSD ([2, 1, 0, 0] : List (Fin 3)) = baseWordValueLSD ([2, 1] : List (Fin 3)) :=
  rfl

example {B : Type} [Fintype B] (w : ℕ → B) (h : IsKAutomaticSequence 2 w) :
    IsCodingOfProlongableKUniformFixedPoint 2 w :=
  (cobham_automatic_iff_uniform_morphic w le_rfl).mp h

example {B : Type} [Fintype B] (w : ℕ → B) (h : IsKAutomaticSequence 3 w) :
    ∃ q : ℕ, ∃ u : ℕ → Fin q, ∃ g : Fin q → B, IsMorphic u g w :=
  h.exists_isMorphic

-- The Thue-Morse morphism `0 ↦ 01`, `1 ↦ 10` read through the morphic-word API.
example {B : Type} [Fintype B] (w : ℕ → B) (u : ℕ → Fin 2) (g : Fin 2 → B)
    (hpre : IsPrefixPreserving (fun x : Fin 2 => [x, 1 - x]) 0)
    (hlim : IsOmegaLimit (fun x : Fin 2 => [x, 1 - x]) 0 u) (hg : ∀ n, w n = g (u n)) :
    IsCodingOfProlongableKUniformFixedPoint 2 w :=
  (isCodingOfProlongableKUniformFixedPoint_iff w le_rfl).mpr
    ⟨2, fun x => [x, 1 - x], fun _ => rfl, 0, u, g, hpre, hlim, hg⟩

end MetaMathlibExt
