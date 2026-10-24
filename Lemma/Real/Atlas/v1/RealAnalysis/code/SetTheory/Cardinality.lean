import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.RealAnalysis.code.SetTheory.Cardinality
open SetTheory SetTheory.Cardinality


namespace SetTheory.Cardinality

/--
[n_lt_two_pow_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Cardinality.lean)
-/
@[path]
lemma n_lt_two_pow_n
  {n : ℕ} :
-- imply
  n < 2 ^ n := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ n ≥ 1 := Nat.one_le_two_pow
    calc n + 1
      _ < 2 ^ n + 1 := by omega
      _ ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

end SetTheory.Cardinality

namespace SetTheory.Cardinality

/--
[cantor_cardinal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Cardinality.lean)
-/
@[path]
lemma cantor_cardinal
  {α : Type*} :
-- imply
  Cardinal.mk α < Cardinal.mk (Set α) := by
-- proof
  rw [Cardinal.mk_set]
  exact Cardinal.cantor (Cardinal.mk α)

end SetTheory.Cardinality

namespace SetTheory.Cardinality

/--
[cantor_schroeder_bernstein](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Cardinality.lean)
-/
@[path]
lemma cantor_schroeder_bernstein
  {f : α → β}
  {g : β → α}
-- given
  (hf : Function.Injective f)
  (hg : Function.Injective g) :
-- imply
  Nonempty (α ≃ β) :=
-- proof
  Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩

end SetTheory.Cardinality


-- created on 2026-10-23
