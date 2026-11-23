/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Def.GroupTheory.ClassFunction.Part2
public import Theorem.Fin.IsClassFunctionCharacter
public import Def.GroupTheory.IrreducibleCharacterBasis
@[expose] public section

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
