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
public import Instance.GroupTheory.IrreducibleCharacterBasis

@[expose] public section

open CategoryTheory
open scoped MonoidAlgebra
open MathlibExt.GroupTheory.ClassFunctionWanted


noncomputable section

universe u v

namespace FDRep

noncomputable def irrCharRegular {G : Type*} [Group G] [Finite G] :
    Representation ℂ G (Shrink.{0} ℂ[G]) :=
  (Shrink.linearEquiv ℂ ℂ[G]).symm.conjRingEquiv.toMonoidHom.comp
    (Representation.leftRegular ℂ G)

noncomputable def irrCharModuleOp {G M : Type*} [Group G] [Finite G]
    [AddCommGroup M] [Module ℂ[G] M] [Module ℂ M] [IsScalarTower ℂ ℂ[G] M]
    (f : G → ℂ) : Module.End ℂ M :=
  ∑ᶠ g, f g • (Representation.ofModule' (k := ℂ) (G := G) M) g⁻¹

end FDRep
end
