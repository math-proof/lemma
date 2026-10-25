import Mathlib
import sympy.Basic
import Def.Combinatorics.Graph.GraphMinor
open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsMinor.refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
lemma IsMinor.refl
  {G : FinGraph} :
-- imply
  IsMinor G G :=
-- proof
  Relation.ReflTransGen.refl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMinor.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
lemma IsMinor.trans
  {H K G : FinGraph} :
-- imply
  IsMinor H K → IsMinor K G → IsMinor H G :=
-- proof
  Relation.ReflTransGen.trans

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMinor.of_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
lemma IsMinor.of_step
  {H G : FinGraph}
-- given
  (h : MinorStep H G) :
-- imply
  IsMinor H G :=
-- proof
  Relation.ReflTransGen.single h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMinor.of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean)
-/
@[path]
lemma IsMinor.of_iso
  {H G : FinGraph}
-- given
  (e : H.G ≃g G.G) :
-- imply
  IsMinor H G :=
-- proof
  IsMinor.of_step (MinorStep.iso H G e)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
