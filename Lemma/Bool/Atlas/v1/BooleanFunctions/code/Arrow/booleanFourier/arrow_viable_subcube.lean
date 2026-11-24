import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.exists_perm_for_valid_triple
open BooleanFourier Bool


/--
[arrow_viable_subcube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
  {u v w : Fin n → Bool}
-- given
  (hm : m ≥ 3)
  (hviable : IsArrowViable f m)
  (hfu : f u = true)
  (hfv : f v = true)
  (hw : ∀ k : Fin n, u k = v k → w k = u k) :
-- imply
  f w = true := by
-- proof
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hexists : ∀ k : Fin n, ∃ σ : Equiv.Perm (Fin m),
    prefersOver σ a b = u k ∧ prefersOver σ b c = v k ∧ prefersOver σ a c = w k :=
    fun k => exists_perm_for_valid_triple (a := a) (b := b) (c := c) (pab := u k) (pbc := v k) (pac := w k) hm hab hbc hac (hw k)
  classical
  let rankings : Fin n → Equiv.Perm (Fin m) := fun k => (hexists k).choose
  have hrankings : ∀ k, prefersOver (rankings k) a b = u k ∧
    prefersOver (rankings k) b c = v k ∧ prefersOver (rankings k) a c = w k :=
    fun k => (hexists k).choose_spec
  have h1 : f (fun k => prefersOver (rankings k) a b) = true := by
    have heq : (fun k => prefersOver (rankings k) a b) = u := funext fun k => (hrankings k).1
    simpa only [heq] using hfu
  have h2 : f (fun k => prefersOver (rankings k) b c) = true := by
    have heq : (fun k => prefersOver (rankings k) b c) = v := funext fun k => (hrankings k).2.1
    simpa only [heq] using hfv
  have h3 : (fun k => prefersOver (rankings k) a c) = w := funext fun k => (hrankings k).2.2
  rw [← h3]; exact hviable rankings a b c hab hbc hac h1 h2


lemma BooleanFourier.arrow_viable_subcube
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
  {u v w : Fin n → Bool}
-- given
  (hm : m ≥ 3)
  (hviable : IsArrowViable f m)
  (hfu : f u = true)
  (hfv : f v = true)
  (hw : ∀ k : Fin n, u k = v k → w k = u k) :
-- imply
  f w = true :=
-- proof
  main hm hviable hfu hfv hw


-- created on 2026-10-23
-- updated on 2026-11-24
