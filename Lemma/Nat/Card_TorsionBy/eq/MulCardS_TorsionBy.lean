import Mathlib
import sympy.Basic


/--
[AddCommGroup_natCard_torsionBy_prod_eq_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddCommGroup_natCard_torsionBy_prod_eq_mul.lean)
-/
@[path]
private lemma main
  {A : Type u} [AddCommGroup A]
  {B : Type v} [AddCommGroup B]
  {N : ℕ} :
-- imply
  Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ)) := by
-- proof
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun x => (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩), fun y => ⟨(y.1.1, y.2.1), ?_⟩, fun x => rfl, fun y => rfl⟩
  · have := x.2; rw [Submodule.mem_torsionBy_iff] at this ⊢; exact (Prod.ext_iff.mp this).1
  · have := x.2; rw [Submodule.mem_torsionBy_iff] at this ⊢; exact (Prod.ext_iff.mp this).2
  · rw [Submodule.mem_torsionBy_iff, Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨(Submodule.mem_torsionBy_iff _ _).mp y.1.2, (Submodule.mem_torsionBy_iff _ _).mp y.2.2⟩


-- created on 2026-10-05
