import Mathlib
import sympy.Basic
import sympy.atlas.RepresentationTheory.Homological.TateCohomology.FiniteCyclic
open CategoryTheory Limits ModuleCat Rep
open TateCohomology


/--
[nonempty_periodicityIso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean)
-/
@[path]
private lemma nonempty_periodicityIso_eq
  [CommGroup G]
  {R G : Type u} [CommRing R] [Group G] [Fintype G] [IsCyclic G]
  {A : Rep R G}
  {n : ℤ} :
-- imply
  Nonempty (tateCohomology A n ≅ tateCohomology A (n + 2)) := by
-- proof
  apply TateCohomology.nonempty_periodicityIso A n


-- created on 2026-10-20
