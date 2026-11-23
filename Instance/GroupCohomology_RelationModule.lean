-- Carved from Lemma/Definitions/Def_GroupCohomology_RelationModule.lean: instance decls only.
module

public import Mathlib
public import Theorem.Rep.RelationModule
public import Def.Rep_RelationModule
@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

section Int

variable {G : Type} [Group G]

instance relationCarrier.instAddCommGroup (B : Rep ℤ G) : AddCommGroup (relationCarrier B) :=
  inferInstanceAs (AddCommGroup (relationModule B))

end Int

end Rep

end
