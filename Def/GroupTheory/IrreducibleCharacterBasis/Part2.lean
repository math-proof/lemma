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
import Instance.GroupTheory.IrreducibleCharacterBasis
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
