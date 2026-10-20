import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Brooks
open Finset
open MathlibExt.Combinatorics.SimpleGraph.BrooksWanted


/--
[brooks](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Brooks.lean)
-/
@[path]
private lemma brooks_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {Δ : ℕ}
-- given
  (hconn : G.Connected)
  (hΔ : ∀ v, G.degree v ≤ Δ)
  (hΔatt : ∃ v, G.degree v = Δ)
  (hcomp : ¬Nonempty (G ≃g (⊤ : SimpleGraph V)))
  (hodd : ∀ (n : ℕ), Odd n → ¬Nonempty (G ≃g SimpleGraph.cycleGraph n)) :
-- imply
  ∃ f : V → Fin Δ, ∀ ⦃v w : V⦄, G.Adj v w → f v ≠ f w := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.BrooksWanted.brooks G Δ hconn hΔ hΔatt hcomp hodd


-- created on 2026-10-20
