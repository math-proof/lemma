/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/GraphMinor.lean -/


import Def.Combinatorics.Graph.GraphMinor
import Lemma.Finset.Graph.GraphMinor


namespace MathlibExtTest.Combinatorics.Graph.GraphMinor

-- Reflexivity: every graph is a minor of itself.
example (G : MetaMathlibExt.FinGraph) : MetaMathlibExt.IsMinor G G :=
  MetaMathlibExt.IsMinor.refl G

-- Transitivity through an intermediate minor.
example {H K G : MetaMathlibExt.FinGraph} :
    MetaMathlibExt.IsMinor H K → MetaMathlibExt.IsMinor K G →
      MetaMathlibExt.IsMinor H G :=
  MetaMathlibExt.IsMinor.trans

-- The identity relabelling is a one-step isomorphism minor.
example (G : MetaMathlibExt.FinGraph) : MetaMathlibExt.IsMinor G G :=
  MetaMathlibExt.IsMinor.of_iso .refl

end MathlibExtTest.Combinatorics.Graph.GraphMinor
