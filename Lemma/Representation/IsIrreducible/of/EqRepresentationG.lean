module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.GroupTheory.BurnsidePaqb.CharacterOrthogonality
open CategoryTheory BurnsidePaqb


public section

/--
[simple_fdrep_of_irreducible](?module=Theorem.GroupTheory.BurnsidePaqb.CharacterOrthogonality)
-/
@[path]
lemma eqRepresentationG_of_isIrreducible
  {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Finite G] (σ : Representation ℂ G V) [σ.IsIrreducible] :
  Simple (FDRep.of σ) := by
  apply simple_fdrep_of_irreducible G σ


-- created on 2026-11-23
