import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped BigOperators


namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[adj_of_adj_of_adj_of_mu_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
# Strongly regular graphs
The definition `SimpleGraph.IsSRGWith` and the complement, parameter-count,
adjacency-matrix equation, and diameter results (`IsSRGWith.compl`,
`IsSRGWith.param_eq`, `IsSRGWith.matrix_eq`, `IsSRGWith.ediam_eq_two`) are in
Mathlib; the connected/`μ = 0`, disconnected-component, and non-principal
eigenvalue results are recorded here.
Sources: no `undergrad.yaml` entry (this topic is absent from the
undergraduate list); A. E. Brouwer and W. H. Haemers, Spectra of Graphs,
Springer 2012, Ch. 9 (strongly regular graphs); C. Godsil and G. Royle,
Algebraic Graph Theory, GTM 207, Ch. 10 (strongly regular graphs).
-/
/-- In a strongly regular graph with `μ = 0`, the endpoints of a nontrivial
two-edge walk are adjacent. -/
lemma _root_.SimpleGraph.IsSRGWith.adj_of_adj_of_adj_of_mu_zero
  {V : Type*} [Fintype V] {n k ℓ : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
  (h : G.IsSRGWith n k ℓ 0) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w)
  (huw : u ≠ w) : G.Adj u w := by
  by_contra huw'
  have hcard := h.of_not_adj huw huw'
  have hv : v ∈ G.commonNeighbors u w :=
    (G.mem_commonNeighbors).2 ⟨huv, hvw.symm⟩
  exact (Fintype.card_eq_zero_iff.mp hcard).false ⟨v, hv⟩

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_walk_eq_or_adj_mu_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_walk_eq_or_adj_mu_zero {V : Type*} [Fintype V] {n k ℓ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith n k ℓ 0)
  {v w : V} (p : G.Walk v w) : v = w ∨ G.Adj v w := by
  induction p with
  | nil => exact Or.inl rfl
  | @cons u v w huv _ ih =>
    obtain rfl | hvw := ih
    · exact Or.inr huv
    · by_cases huw : u = w
      · exact Or.inl huw
      · exact Or.inr (h.adj_of_adj_of_adj_of_mu_zero huv hvw huw)

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_eq_top_of_connected_mu_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_eq_top_of_connected_mu_zero
  {V : Type*} [Fintype V] {n k ℓ : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
  (h : G.IsSRGWith n k ℓ 0) (hconn : G.Connected) : G = ⊤ := by
  ext v w
  constructor
  · exact fun hvw => hvw.ne
  · intro hvw
    obtain rfl | hvw' := (hconn.preconnected v w).elim (srg_walk_eq_or_adj_mu_zero h)
    · exact (hvw rfl).elim
    · exact hvw'

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_sum_eq_zero_of_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_sum_eq_zero_of_eigenvector
  {V : Type*} [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj] {k : ℕ} (hreg : G.IsRegularOfDegree k) {x : ℂ}
  (hx : x ≠ (k : ℂ)) {v : V → ℂ}
  (hv : (G.adjMatrix ℂ).mulVec v = x • v) : (∑ i, v i) = 0 := by
  classical
  have hleft : Matrix.vecMul (fun _ : V => (1 : ℂ)) (G.adjMatrix ℂ) =
    fun _ => (k : ℂ) := by
    funext i
    simp [hreg i]
  have hdot := Matrix.dotProduct_mulVec (fun _ : V => (1 : ℂ)) (G.adjMatrix ℂ) v
  rw [hv, hleft] at hdot
  have hsum : x * (∑ i, v i) = (k : ℂ) * ∑ i, v i := by
    simpa [dotProduct, Finset.mul_sum] using hdot
  have hprod : (x - (k : ℂ)) * (∑ i, v i) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr hsum
  obtain h | h := mul_eq_zero.mp hprod
  · exact (sub_ne_zero.mpr hx h).elim
  · exact h

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_of_one_mulVec_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_of_one_mulVec_eq_zero
  {V : Type*} [Fintype V] {v : V → ℂ} (hv : (∑ i, v i) = 0) :
  (Matrix.of (1 : V → V → ℂ)).mulVec v = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, hv]

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_compl_mulVec_eq_neg_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_compl_mulVec_eq_neg_add
  {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] {x : ℂ} {v : V → ℂ} (hvsum : (∑ i, v i) = 0)
  (hv : (G.adjMatrix ℂ).mulVec v = x • v) :
  (Gᶜ.adjMatrix ℂ).mulVec v = -(v + x • v) := by
  have hmat := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℂ
  rw [G.compl_adjMatrix_eq_adjMatrix_compl ℂ] at hmat
  have happ := congrArg (fun M : Matrix V V ℂ => M.mulVec v) hmat
  simp only [Matrix.add_mulVec, Matrix.one_mulVec] at happ
  rw [hv, srg_of_one_mulVec_eq_zero hvsum] at happ
  simpa only [zero_add] using eq_neg_of_add_eq_zero_right happ

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_eigenvector_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
private lemma srg_eigenvector_quadratic
  {V : Type*} [Fintype V] {n k ℓ μ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith n k ℓ μ)
  {x : ℂ} (hx : x ≠ (k : ℂ)) {v : V → ℂ} (hv0 : v ≠ 0)
  (hv : (G.adjMatrix ℂ).mulVec v = x • v) :
  x ^ 2 = ((ℓ : ℂ) - (μ : ℂ)) * x + ((k : ℂ) - (μ : ℂ)) := by
  classical
  have hvsum := srg_sum_eq_zero_of_eigenvector h.regular hx hv
  have hvcompl := srg_compl_mulVec_eq_neg_add hvsum hv
  have hmat := h.matrix_eq (α := ℂ)
  have happ := congrArg (fun M : Matrix V V ℂ => M.mulVec v) hmat
  simp only [pow_two, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at happ
  rw [hvcompl] at happ
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa only [Pi.zero_apply] using (Function.ne_iff.mp hv0)
  have happi := congrFun happ i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nsmul_eq_mul] at happi
  apply mul_right_cancel₀ hi
  calc
    x ^ 2 * v i = x * (x * v i) := by ring
    _ = (k : ℂ) * v i + (ℓ : ℂ) * (x * v i) +
      (μ : ℂ) * -(v i + x * v i) := happi
    _ = (((ℓ : ℂ) - (μ : ℂ)) * x + ((k : ℂ) - (μ : ℂ))) * v i := by ring

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[nonprincipal_eigenvalue_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
satisfies the standard strongly regular graph quadratic. -/
lemma _root_.SimpleGraph.IsSRGWith.nonprincipal_eigenvalue_quadratic
  {V : Type*} [Fintype V] {n k ℓ μ : ℕ} {G : SimpleGraph V}
  [DecidableRel G.Adj] [DecidableEq V] (h : G.IsSRGWith n k ℓ μ) {x : ℂ}
  (hx : x ≠ (k : ℂ))
  (hEig : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℂ)) x) :
  x ^ 2 = ((ℓ : ℂ) - (μ : ℂ)) * x + ((k : ℂ) - (μ : ℂ)) := by
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hvapp := hv.apply_eq_smul
  rw [Matrix.toLin'_apply] at hvapp
  exact srg_eigenvector_quadratic h hx hv.2 hvapp

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_connected_mu_zero_complete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
lemma srg_connected_mu_zero_complete
  [Fintype V]
  {n k ℓ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (h : G.IsSRGWith n k ℓ 0)
  (hconn : G.Connected) :
-- imply
  G = ⊤ :=
-- proof
srg_eq_top_of_connected_mu_zero h hconn

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_reachable_eq_or_adj_mu_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
lemma srg_reachable_eq_or_adj_mu_zero
  [Fintype V]
  {n k ℓ : ℕ}
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {v w : V}
-- given
  (h : G.IsSRGWith n k ℓ 0)
  (hre : G.Reachable v w) :
-- imply
  v = w ∨ G.Adj v w :=
-- proof
hre.elim (srg_walk_eq_or_adj_mu_zero h)

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

/--
[srg_nonprincipal_eigenvalue_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StronglyRegular.lean)
-/
@[path]
lemma srg_nonprincipal_eigenvalue_quadratic
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
  exact h.nonprincipal_eigenvalue_quadratic hx hEig

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

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


-- created on 2026-10-20
-- updated on 2026-10-26
