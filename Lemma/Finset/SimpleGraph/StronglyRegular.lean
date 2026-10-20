import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.StronglyRegular
open scoped BigOperators
open MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted


/--
[_root_.SimpleGraph.IsSRGWith.adj_of_adj_of_adj_of_mu_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma SimpleGraph_IsSRGWith_adj_of_adj_of_adj_of_mu_zero_eq
  [Fintype V]
  {n k ℓ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {u v w : V}
-- given
  (h : G.IsSRGWith n k ℓ 0)
  (huv : G.Adj u v)
  (hvw : G.Adj v w)
  (huw : u ≠ w) :
-- imply
  G.Adj u w := by
-- proof
  apply SimpleGraph.IsSRGWith.adj_of_adj_of_adj_of_mu_zero h huv hvw huw

/--
[_root_.SimpleGraph.IsSRGWith.nonprincipal_eigenvalue_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma SimpleGraph_IsSRGWith_nonprincipal_eigenvalue_quadratic_eq
  [Fintype V] [DecidableEq V]
  {n k ℓ μ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {x : ℂ}
-- given
  (h : G.IsSRGWith n k ℓ μ)
  (hx : x ≠ (k : ℂ))
  (hEig : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℂ)) x) :
-- imply
  x ^ 2 = ((ℓ : ℂ) - (μ : ℂ)) * x + ((k : ℂ) - (μ : ℂ)) := by
-- proof
  apply SimpleGraph.IsSRGWith.nonprincipal_eigenvalue_quadratic h hx hEig

/--
[srg_connected_mu_zero_complete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_connected_mu_zero_complete_eq
  [Fintype V]
  {n k ℓ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (h : G.IsSRGWith n k ℓ 0)
  (hconn : G.Connected) :
-- imply
  G = ⊤ := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted.srg_connected_mu_zero_complete G h hconn

/--
[srg_reachable_eq_or_adj_mu_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_reachable_eq_or_adj_mu_zero_eq
  [Fintype V]
  {n k ℓ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {v w : V}
-- given
  (h : G.IsSRGWith n k ℓ 0)
  (hre : G.Reachable v w) :
-- imply
  v = w ∨ G.Adj v w := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted.srg_reachable_eq_or_adj_mu_zero G h v w hre

/--
[srg_nonprincipal_eigenvalue_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_nonprincipal_eigenvalue_quadratic_eq
  [Fintype V] [DecidableEq V]
  {n k ℓ μ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {x : ℂ}
-- given
  (h : G.IsSRGWith n k ℓ μ)
  (hconn : G.Connected)
  (hncomp : G ≠ ⊤)
  (hx : x ≠ (k : ℂ))
  (hEig : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℂ)) x) :
-- imply
  x ^ 2 = (((ℓ : ℂ) - (μ : ℂ)) * x + (((k : ℂ) - (μ : ℂ)))) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted.srg_nonprincipal_eigenvalue_quadratic G h hconn hncomp x hx hEig


-- created on 2026-10-20
