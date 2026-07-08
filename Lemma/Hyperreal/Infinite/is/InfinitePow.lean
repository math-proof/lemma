import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
open Hyperreal


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfinitePow |
| comm | Hyperreal.InfinitePow.is.Infinite |
| mp   | Hyperreal.InfinitePow.of.Infinite |
| mpr  | Hyperreal.Infinite.of.InfinitePow |
| mp.mt | Hyperreal.NotInfinite.of.NotInfinitePow |
| mpr.mt | Hyperreal.NotInfinitePow.of.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [NeZero (n : ℕ)]
-- given
  (x : ℝ*) :
-- imply
  x → ∞ ↔ (x ^ n) → ∞ := by
-- proof
  have h_n := NeZero.ne n
  constructor <;>
    intro h
  ·
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      simp [pow_succ]
      if h_n : n = 0 then
        subst h_n
        simp_all
      else
        have ih := ih h_n
        apply InfiniteMul.of.Infinite.Infinite ih h
  ·
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      if h_n : n = 0 then
        subst h_n
        simp_all
      else
        have ih := ih h_n
        by_contra h_x_nf
        have h_x' : ¬(x → ∞) := h_x_nf
        have h_pn : (x ^ n) → ∞ := by
          by_contra h_pn_nf
          have h_prod_nf := NotInfiniteMul.of.NotInfinite.NotInfinite h_pn_nf h_x'
          have h_prod : ((x ^ n) * x) → ∞ := by simpa [pow_succ] using h
          exact h_prod_nf h_prod
        exact h_x_nf (ih h_pn)


-- created on 2025-12-16
-- updated on 2025-12-17
