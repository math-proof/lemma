module
public import Mathlib
public import Theorem.GroupTheory.BurnsidePaqb.CharacterOrthogonality
open CategoryTheory BurnsidePaqb


/--
[simple_fdrep_of_irreducible](?module=Theorem.GroupTheory.BurnsidePaqb.CharacterOrthogonality)
-/
public theorem eqRepresentationG_of_isIrreducible
  {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Finite G] (σ : Representation ℂ G V) [σ.IsIrreducible] :
-- imply
  Simple (FDRep.of σ) := by
-- proof
  apply simple_fdrep_of_irreducible G σ


-- created on 2026-11-23
