import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.ErdosGirthChromatic
open Finset
open MathlibExt.Combinatorics.SimpleGraph.ErdosGirthChromaticWanted


/--
[erdos_high_girth_chromatic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ErdosGirthChromatic.lean)
-/
@[path]
private lemma erdos_high_girth_chromatic_eq
  {k g : ℕ}
-- given
  (hg : 3 ≤ g) :
-- imply
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    g ≤ G.girth ∧ (k : ℕ∞) ≤ G.chromaticNumber := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.ErdosGirthChromaticWanted.erdos_high_girth_chromatic k g hg


-- created on 2026-10-20
