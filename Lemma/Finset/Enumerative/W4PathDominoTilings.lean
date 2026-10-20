import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.W4PathDominoTilings
open SimpleGraph
open MetaMathlibExt


/--
[boxProd_tiling_card_eq_fib_mul_pellNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma boxProd_tiling_card_eq_fib_mul_pellNumber_eq
  :
-- imply
  ∀ (n : ℕ) (_hn : 2 ≤ n),
    Nat.card { M : (((SimpleGraph.completeGraph (Fin 4)).deleteEdges
    {Sym2.mk (0 : Fin 4) (1 : Fin 4)} □
    SimpleGraph.pathGraph (n - 1)).Subgraph) // M.IsPerfectMatching } =
    Nat.fib n * pellNumber n := by
-- proof
  apply MetaMathlibExt.boxProd_tiling_card_eq_fib_mul_pellNumber

/--
[boxProd_tiling_card_eq_fib_mul_pell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma boxProd_tiling_card_eq_fib_mul_pell_eq
  :
-- imply
  ∀ (n : ℕ) (_hn : 2 ≤ n),
    Nat.card { M : (((SimpleGraph.completeGraph (Fin 4)).deleteEdges
    {Sym2.mk (0 : Fin 4) (1 : Fin 4)} □
    SimpleGraph.pathGraph (n - 1)).Subgraph) // M.IsPerfectMatching } =
    Nat.fib n *
    ((Nat.rec (motive := by
-- proof
  apply MetaMathlibExt.boxProd_tiling_card_eq_fib_mul_pell


-- created on 2026-10-20
