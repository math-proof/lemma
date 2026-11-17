/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HajnalSzemeredi.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Relation
public import Def.Combinatorics.SimpleGraph.HajnalSzemeredi

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted

noncomputable instance hsSub_dec {V' : Type*} [DecidableEq V']
    (G' : SimpleGraph V') (S : Finset V') :
    DecidableRel (hsSub G' S).Adj :=
  fun _ _ => Classical.propDecidable _

end MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted
