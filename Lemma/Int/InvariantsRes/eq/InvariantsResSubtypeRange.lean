import Mathlib
import sympy.Basic

open scoped Classical TensorProduct
open CategoryTheory CategoryTheory.MonoidalCategory Module

/--
[Rep_invariants_res_eq_invariants_res_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_invariants_res_eq_invariants_res_range.lean)
-/
@[path]
private lemma main
  [CommRing k]
  {G D' : Type} [Group G] [Group D']
  {φ : D' →* G}
  {X : Rep.{0} k G} :
-- imply
  (Rep.res φ X).ρ.invariants = (Rep.res φ.range.subtype X).ρ.invariants := by
-- proof
  ext v
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]
  constructor
  · rintro h ⟨g, d, rfl⟩
    exact h d
  · intro h d
    exact h ⟨φ d, d, rfl⟩


-- created on 2026-10-05
