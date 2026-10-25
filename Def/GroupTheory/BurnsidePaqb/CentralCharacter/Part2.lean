/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean -/

import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorem.GroupTheory.BurnsidePaqb.ClassSum.Part3
import Lemma.Nat.ConjClass.of.IsConj
import Theorem.GroupTheory.BurnsidePaqb.CentralCharacter.Part2
/-!
Central-character stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/CentralChar.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

section CentralScalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

open Classical in
/-- The finite set of scalars spanning the integrality subalgebra. -/
noncomputable def scalarGens : Finset ℂ :=
  insert 1 (Finset.univ.image (centralScalar ρ))

end CentralScalar
end BurnsidePaqb
