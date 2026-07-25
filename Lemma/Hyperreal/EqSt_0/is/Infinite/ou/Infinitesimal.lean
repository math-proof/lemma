import sympy.series.limits
import sympy.core.singleton
import Lemma.Bool.Iff.is.IffNotS
open Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.EqSt_0.is.Infinite.ou.Infinitesimal |
| comm | Hyperreal.Infinite.ou.Infinitesimal.is.EqSt_0 |
| mp   | Hyperreal.Infinite.ou.Infinitesimal.of.EqSt_0 |
| mpr  | Hyperreal.EqSt_0.of.Infinite.ou.Infinitesimal |
| mp.mt | Hyperreal.NeSt_0.of.NotInfinite.NotInfinitesimal |
| mpr.mt  | Hyperreal.NotInfinite.NotInfinitesimal.of.NeSt_0 |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  stdPart x = 0 ↔ x → ∞ ∨ x → 0 := by
-- proof
  rw [Iff.is.IffNotS]
  simp


-- created on 2025-12-18
