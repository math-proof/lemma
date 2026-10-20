import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.CentralCharacter
open BurnsidePaqb


/--
[exists_scalar_of_central](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma exists_scalar_of_central_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {z : MonoidAlgebra ℂ G}
-- given
  (hz : ∀ w, w * z = z * w) :
-- imply
  ∃ c : ℂ, ∀ v : V, ρ.asAlgebraHom z v = c • v := by
-- proof
  apply BurnsidePaqb.exists_scalar_of_central ρ z hz

/--
[centralScalar_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma centralScalar_spec_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G}
  {v : V} :
-- imply
  ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) v
    = centralScalar ρ l • v := by
-- proof
  apply BurnsidePaqb.centralScalar_spec ρ l v

/--
[centralScalar_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma centralScalar_mul_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l1 l2 : ConjClasses G} :
-- imply
  centralScalar ρ l1 * centralScalar ρ l2
    = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
    (classRep l) : ℂ) * centralScalar ρ l := by
-- proof
  apply BurnsidePaqb.centralScalar_mul ρ l1 l2

/--
[centralScalar_trace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma centralScalar_trace_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  centralScalar ρ l * Module.finrank ℂ V
    = ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x := by
-- proof
  apply BurnsidePaqb.centralScalar_trace ρ l

/--
[one_mem_scalarSpan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma one_mem_scalarSpan_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  (1 : ℂ) ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
-- proof
  apply BurnsidePaqb.one_mem_scalarSpan ρ

/--
[scalar_mem_scalarSpan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma scalar_mem_scalarSpan_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  centralScalar ρ l ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
-- proof
  apply BurnsidePaqb.scalar_mem_scalarSpan ρ l

/--
[scalarGens_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma scalarGens_mul_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {a b : ℂ}
-- given
  (ha : a ∈ scalarGens ρ)
  (hb : b ∈ scalarGens ρ) :
-- imply
  a * b ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
-- proof
  apply BurnsidePaqb.scalarGens_mul ρ a b ha hb

/--
[scalarSubalg_fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma scalarSubalg_fg_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  (scalarSubalg ρ).toSubmodule.FG := by
-- proof
  apply BurnsidePaqb.scalarSubalg_fg ρ

/--
[centralScalar_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma centralScalar_isIntegral_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  IsIntegral ℤ (centralScalar ρ l) := by
-- proof
  apply BurnsidePaqb.centralScalar_isIntegral ρ l

/--
[classSum_centralScalar_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma classSum_centralScalar_isIntegral_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G} :
-- imply
  IsIntegral ℤ ((conjClass g).card * ρ.character g / ρ.character 1) := by
-- proof
  apply BurnsidePaqb.classSum_centralScalar_isIntegral ρ g


-- created on 2026-10-20
