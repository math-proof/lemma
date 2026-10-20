import Mathlib
import sympy.Basic
import sympy.atlas.Probability.MeanShortChords
open MetaMathlibExt


/--
[mean_short_chords_in_linear_k_chord_diagrams](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/MeanShortChords.lean)
-/
@[path]
private lemma mean_short_chords_in_linear_k_chord_diagrams_eq
  {k n : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  let diagrams := by
-- proof
  apply MetaMathlibExt.mean_short_chords_in_linear_k_chord_diagrams k n hk


-- created on 2026-10-20
