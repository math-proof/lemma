/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/StronglyRegular.lean -/


import Lemma.Finset.SimpleGraph.StronglyRegular


-- The Petersen parameters force every nonprincipal adjacency eigenvalue to be `1` or `-2`.
example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq V] (h : G.IsSRGWith 10 3 0 1) (x : ℂ) (hx : x ≠ 3)
    (hEig : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℂ)) x) :
    x = 1 ∨ x = -2 := by
  have hquad := h.nonprincipal_eigenvalue_quadratic hx hEig
  norm_num at hquad
  have hfactor : (x - 1) * (x + 2) = 0 := by
    calc
      (x - 1) * (x + 2) = x ^ 2 + x - 2 := by ring
      _ = 0 := by rw [hquad]; ring
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

-- Distinct nonadjacent vertices in a strongly regular graph with `μ = 0` are not reachable.
example {V : Type*} [Fintype V] {n k ℓ : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.IsSRGWith n k ℓ 0) {v w : V}
    (hne : v ≠ w) (hnadj : ¬G.Adj v w) : ¬G.Reachable v w := by
  intro hre
  apply hre.elim
  intro p
  have hwalk : ∀ {a b : V}, G.Walk a b → a = b ∨ G.Adj a b := by
    intro a b q
    induction q with
    | nil => exact Or.inl rfl
    | @cons u z w huz _ ih =>
        rcases ih with rfl | hzw
        · exact Or.inr huz
        · by_cases huw : u = w
          · exact Or.inl huw
          · exact Or.inr (h.adj_of_adj_of_adj_of_mu_zero huz hzw huw)
  exact (hwalk p).elim hne hnadj

