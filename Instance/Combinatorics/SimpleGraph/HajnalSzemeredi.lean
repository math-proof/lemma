/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HajnalSzemeredi.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Def.Combinatorics.SimpleGraph.HajnalSzemeredi


namespace MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted

noncomputable instance hsSub_dec {V' : Type*} [DecidableEq V']
    (G' : SimpleGraph V') (S : Finset V') :
    DecidableRel (hsSub G' S).Adj :=
  fun _ _ => Classical.propDecidable _

end MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted
