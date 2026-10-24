import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Dichromatic
open SimpleGraph


namespace SimpleGraph

/--
[DichromaticColorable.dichromaticNumber_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dichromatic.lean)
-/
@[path]
lemma DichromaticColorable.dichromaticNumber_eq_sInf
  {G : SimpleGraph V}
  {n : ℕ}
-- given
  (h : G.DichromaticColorable n) :
-- imply
  G.dichromaticNumber = sInf {n' : ℕ | G.DichromaticColorable n'} := by
-- proof
  rw [ENat.natCast_sInf, dichromaticNumber]
  exact ⟨_, h⟩

end SimpleGraph

namespace SimpleGraph

/--
[IsOrientation.of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dichromatic.lean)
-/
@[path]
lemma IsOrientation.of_edgeless
  {G : SimpleGraph V}
-- given
  (hempty : ∀ u v, ¬ G.Adj u v) :
-- imply
  G.IsOrientation (fun _ _ => False) := by
-- proof
  refine ⟨fun u v h => absurd h (by simp), fun u v hadj => ?_⟩
  exact absurd hadj (hempty u v)

end SimpleGraph

namespace SimpleGraph

/--
[DichromaticColorable.of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dichromatic.lean)
-/
@[path]
lemma DichromaticColorable.of_edgeless
  {G : SimpleGraph V}
-- given
  (hempty : ∀ u v, ¬ G.Adj u v) :
-- imply
  G.DichromaticColorable 1 := by
-- proof
  intro D hD
  refine ⟨fun _ => 0, fun n f hdir => ?_⟩
  have i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  have e : D (f i0.castSucc) (f i0.succ) := hdir.2 i0
  exact absurd (hD.1 _ _ e) (hempty _ _)

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
