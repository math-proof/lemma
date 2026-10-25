/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Shrink
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RepresentationTheory.FinGroupCharZero
import Def.GroupTheory.ClassFunction.Part2
import Lemma.Fin.IsClassFunctionCharacter
import Def.GroupTheory.IrreducibleCharacterBasis
open CategoryTheory
open scoped MonoidAlgebra
open MathlibExt.GroupTheory.ClassFunctionWanted


noncomputable section

universe u v

namespace FDRep

noncomputable instance irrCharSmallMonoidAlgebra {G : Type*} [Finite G] :
    Small.{0} ℂ[G] :=
  (small_congr MonoidAlgebra.coeffEquiv).mpr inferInstance

end FDRep
end
