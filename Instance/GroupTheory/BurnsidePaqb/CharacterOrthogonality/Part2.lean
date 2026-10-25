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
import Theorem.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part3
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

/-- The trivial representation is irreducible: submodules of `ℂ` are `⊥`/`⊤`. -/
instance trivial_isIrreducible : (Representation.trivial ℂ G ℂ).IsIrreducible :=
  @IsSimpleOrder.of_forall_eq_top _ _ _
    ⟨⊤, ⊥, fun h => by
      have htop : (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule
          = ⊤ := rfl
      have hbot : (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule
          = ⊥ := rfl
      have hsub : (⊤ : Submodule ℂ ℂ) = ⊥ := by rw [← htop, ← hbot, h]
      have h1 : (1 : ℂ) ∈ (⊤ : Submodule ℂ ℂ) := Submodule.mem_top
      rw [hsub] at h1
      simp at h1⟩
    fun U hU => by
      rcases eq_bot_or_eq_top U.toSubmodule with h | h
      · exfalso
        apply hU
        have hU' : U.toSubmodule
            = (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule := by
          rw [h]; rfl
        exact Subrepresentation.toSubmodule_injective hU'
      · have hU' : U.toSubmodule
            = (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule := by
          rw [h]; rfl
        exact Subrepresentation.toSubmodule_injective hU'

end BurnsidePaqb
