/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Def.Algebra.Lie.LeviDecomposition.Part15
import Lemma.Fin.EqSum_SMul.of.Basis
import Def.Algebra.Lie.Ado
attribute [local instance 100] LieRing.ofAssociativeRing

/-!
# Ado's theorem

This file proves Ado's theorem over fields of characteristic zero. It builds finite-dimensional
representations from quotients of universal enveloping algebras, then uses the Levi decomposition.
-/


namespace MathlibExt.Algebra.Lie.LandmarkWanted

theorem adoUniversalLift_fst
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) (u : UniversalEnvelopingAlgebra K L) :
    (adoUniversalLift D u).fst = u := by
  let f := (TrivSqZeroExt.fstHom K (UniversalEnvelopingAlgebra K L)
    (UniversalEnvelopingAlgebra K L)).comp (adoUniversalLift D)
  have hf : f = AlgHom.id K (UniversalEnvelopingAlgebra K L) := by
    apply UniversalEnvelopingAlgebra.hom_ext K
    ext x
    change (adoUniversalLift D (UniversalEnvelopingAlgebra.ι K x)).fst =
      UniversalEnvelopingAlgebra.ι K x
    rw [adoUniversalLift, UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  exact DFunLike.congr_fun hf u

end MathlibExt.Algebra.Lie.LandmarkWanted
