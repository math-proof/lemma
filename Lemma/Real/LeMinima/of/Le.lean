import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic
import Lemma.Real.LeMinimaS.of.All_Le


@[main]
private lemma main
  {n : ℤ}
  {f g : ℤ → ℝ}
-- given
  (hn : 0 ≤ n)
  (h : ∀ i ∈ Finset.Icc 0 n, f i ≤ g i) :
-- imply
  Minima (Finset.Icc 0 n : Set ℤ) f ≤ Minima (Finset.Icc 0 n : Set ℤ) g := by
-- proof
  have hne : (Finset.Icc (0 : ℤ) n : Set ℤ).Nonempty :=
    ⟨0, Finset.mem_Icc.mpr ⟨by linarith, hn⟩⟩
  have hfin : (f '' (Finset.Icc (0 : ℤ) n : Set ℤ)).Finite :=
    (Finset.finite_toSet _).image f
  exact Real.LeMinimaS.of.All_Le hne hfin.bddBelow h


-- created on 2023-04-23
