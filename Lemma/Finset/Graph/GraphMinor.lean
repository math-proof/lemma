import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Graph.GraphMinor
open MetaMathlibExt


/--
[IsMinor.refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
private lemma IsMinor_refl_eq
  {G : FinGraph} :
-- imply
  IsMinor G G := by
-- proof
  apply MetaMathlibExt.IsMinor.refl G

/--
[IsMinor.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
private lemma IsMinor_trans_eq
  {H K G : FinGraph} :
-- imply
  IsMinor H K → IsMinor K G → IsMinor H G := by
-- proof
  apply MetaMathlibExt.IsMinor.trans

/--
[IsMinor.of_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
private lemma IsMinor_of_step_eq
  {H G : FinGraph}
-- given
  (h : MinorStep H G) :
-- imply
  IsMinor H G := by
-- proof
  apply MetaMathlibExt.IsMinor.of_step h

/--
[IsMinor.of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
private lemma IsMinor_of_iso_eq
  {H G : FinGraph}
-- given
  (e : H.G ≃g G.G) :
-- imply
  IsMinor H G := by
-- proof
  apply MetaMathlibExt.IsMinor.of_iso e


-- created on 2026-10-20
