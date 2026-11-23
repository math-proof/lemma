/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean -/

module

public import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Complex.Basic
public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Theorem.GroupTheory.BurnsidePaqb.CharacterOrthogonality

@[expose] public section

open CategoryTheory

/-!
Character-orthogonality stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ColumnOrth.lean`.
-/


namespace BurnsidePaqb

variable (G : Type) [Group G] [Fintype G]

/-- Isomorphism classes of simple `FDRep`s: two simples are related when isomorphic. -/
def Simple.isoSetoid : Setoid {V : FDRep ℂ G // Simple V} where
  r S T := Nonempty (S.1 ≅ T.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun h => h.elim fun i => ⟨i.symm⟩,
    fun h1 h2 => h1.elim fun i => h2.elim fun j => ⟨i.trans j⟩⟩

/-- Iso-classes of simple finite-dimensional complex representations. -/
def Irr : Type 1 := Quotient (Simple.isoSetoid G)

/-- Character of a class, well-defined by `FDRep.char_iso`. -/
noncomputable def Irr.charFun (c : Irr G) : G → ℂ :=
  Quotient.lift (fun S => S.1.character) (fun S T h => by
    obtain ⟨i⟩ := h
    exact FDRep.char_iso i) c

end BurnsidePaqb
