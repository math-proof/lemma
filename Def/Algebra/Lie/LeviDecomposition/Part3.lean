/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part3
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

def leviZeroFitting
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (c : Module.End K M)
    (hc : ∀ x : L, Commute c (LieModule.toEnd K L M x)) : LieSubmodule K L M where
  __ := c.maxGenEigenspace 0
  lie_mem := by
    intro x m hm
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc x) 0 hm

end LeviDecomposition
