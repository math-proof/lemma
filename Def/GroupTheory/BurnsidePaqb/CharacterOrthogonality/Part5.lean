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
public import Instance.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part3
open CategoryTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean -/
/-!
Character-orthogonality stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ColumnOrth.lean`.
-/
namespace BurnsidePaqb

variable (G : Type) [Group G] [Fintype G]

/-- Zimmerman's averaging operator for a function `f`. -/
noncomputable def zimmOp (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (f : G → ℂ) :
    Module.End ℂ M :=
  ∑ g : G, f g • (Representation.ofModule' (k := ℂ) M) g⁻¹

end BurnsidePaqb
