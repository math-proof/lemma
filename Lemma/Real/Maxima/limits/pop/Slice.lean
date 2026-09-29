import sympy.concrete.expr_with_limits
import sympy.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Pi


@[main]
private lemma main
  [Fintype D] [Nonempty D] [DecidableEq D]
  {k : ℕ}
  {f : (Fin (k + 1) → D) → ℝ} :
-- imply
  Maxima Set.univ f = Maxima Set.univ fun a : D => Maxima Set.univ fun v : Fin k → D => f (Fin.snoc v a) := by
-- proof
  unfold Maxima
  simp only [Set.image_univ]
  change (⨆ w, f w) = ⨆ a : D, ⨆ v : Fin k → D, f (Fin.snoc v a)
  have hb : ∀ a : D, BddAbove (Set.range fun v : Fin k → D => f (Fin.snoc v a)) := fun a => Set.finite_range _ |>.bddAbove
  apply le_antisymm
  ·
    refine ciSup_le fun w => ?_
    have hw : w = Fin.snoc (Fin.init w) (w (Fin.last k)) := (Fin.snoc_init_self w).symm
    calc f w = f (Fin.snoc (Fin.init w) (w (Fin.last k))) := by rw [← hw]
      _ ≤ ⨆ v : Fin k → D, f (Fin.snoc v (w (Fin.last k))) := le_ciSup (hb _) (Fin.init w)
      _ ≤ ⨆ a : D, ⨆ v : Fin k → D, f (Fin.snoc v a) := le_ciSup (f := fun a : D => ⨆ v : Fin k → D, f (Fin.snoc v a)) (Set.finite_range _).bddAbove (w (Fin.last k))
  ·
    refine ciSup_le fun a => ciSup_le fun v => ?_
    exact le_ciSup (Set.finite_range f).bddAbove (Fin.snoc v a)


-- created on 2026-09-27
