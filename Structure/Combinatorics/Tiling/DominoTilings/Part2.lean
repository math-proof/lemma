import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part5
open Finset BigOperators


namespace DominoTilings

structure DominoTiling (n m : ℕ) where
  
  dominos : Finset Domino
  
  dominos_in_rect : ∀ d ∈ dominos, d.cells ⊆ Rectangle n m
  
  covers_all : (dominos.biUnion Domino.cells) = Rectangle n m
  
  pairwise_disjoint : ∀ d₁ ∈ dominos, ∀ d₂ ∈ dominos, d₁ ≠ d₂ → Disjoint d₁.cells d₂.cells

end DominoTilings
