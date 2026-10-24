import Mathlib
import sympy.Basic
open scoped ComplexConjugate


/--
[Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite.lean)
-/
@[path]
private lemma main
  [AddCommGroup E] [Module ℂ E]
  {V : Submodule ℂ E}
  {B : E → E → ℂ}
  {D : ℕ}
-- given
  (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
  (hsmul : ∀ (c : ℂ) (x y : E), B (c • x) y = c * B x y)
  (hsymm : ∀ x y, B y x = conj (B x y))
  (hpos : ∀ x ∈ V, 0 ≤ (B x x).re)
  (hdef : ∀ x ∈ V, B x x = 0 → x = 0)
  (hD : ∀ (n : ℕ) (e : Fin n → E), (∀ i, e i ∈ V) → (∀ i j, B (e i) (e j) = if i = j then 1 else 0) → n ≤ D) :
-- imply
  FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ D := by
-- proof
  classical
    let core : InnerProductSpace.Core ℂ V :=
      { inner := fun x y => B (y : E) (x : E)
        conj_inner_symm := fun x y => (hsymm (x : E) (y : E)).symm
        re_inner_nonneg := fun x => hpos x x.2
        add_left := fun x y z => by
          change B (z : E) ((x : E) + (y : E)) = B (z : E) (x : E) + B (z : E) (y : E)
          rw [hsymm ((x : E) + (y : E)) (z : E), hadd, map_add, ← hsymm, ← hsymm]
        smul_left := fun x y r => by
          change B (y : E) (r • (x : E)) = conj r * B (y : E) (x : E)
          rw [hsymm (r • (x : E)) (y : E), hsmul, map_mul, ← hsymm]
        definite := fun x hx => Subtype.ext (by exact_mod_cast hdef x x.2 hx) }
    let : NormedAddCommGroup V := core.toNormedAddCommGroup
    let : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
    have hli : ∀ s : Finset V, (LinearIndependent ℂ fun i : s => (i : V)) → s.card ≤ D := by
      intro s hs
      set n := s.card
      let e : Fin n ≃ s := (s.equivFin).symm
      have hs' : LinearIndependent ℂ (fun i : Fin n => ((e i : s) : V)) := hs.comp e e.injective
      have hon := InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℂ) (E := ↥V) hs'
      rw [orthonormal_iff_ite] at hon
      refine hD n (fun i => ((InnerProductSpace.gramSchmidtNormed ℂ (fun i : Fin n => ((e i : s) : V)) i : V) : E))
        (fun i => Subtype.mem _) (fun i j => ?_)
      have := hon j i
      change B _ _ = _ at this
      rw [this]
      if h : i = j then
        subst h; simp
      else
        rw [if_neg (Ne.symm h), if_neg h]
    have hrank : Module.rank ℂ V ≤ D := rank_le hli
    refine ⟨?_, Module.finrank_le_of_rank_le hrank⟩
    rw [← Module.rank_lt_aleph0_iff]
    exact hrank.trans_lt (Cardinal.natCast_lt_aleph0 (n := D))


-- created on 2026-10-23
