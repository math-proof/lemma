/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean -/

import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Instance.GroupTheory.BurnsidePaqb.CharacterOrthogonality
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

omit [Fintype G] in
/-- Bridge (forward): an irreducible complex representation gives a simple `FDRep`. -/
theorem simple_fdrep_of_irreducible {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Finite G] (σ : Representation ℂ G V) [σ.IsIrreducible] :
    Simple (FDRep.of σ) := by
  rw [FDRep.simple_iff_end_is_rank_one]
  have e1 := Representation.linHom.invariantsEquivFDRepHom (FDRep.of σ) (FDRep.of σ)
  have e2 := Representation.invariantsEquivIntertwiningMap (FDRep.of σ).ρ (FDRep.of σ).ρ
  rw [← LinearEquiv.finrank_eq e1, LinearEquiv.finrank_eq e2]
  change Module.finrank ℂ (σ.IntertwiningMap σ) = 1
  exact Representation.IsIrreducible.finrank_intertwiningMap_self σ

end BurnsidePaqb
