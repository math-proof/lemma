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
import sympy.atlas.GroupTheory.ClassFunction
import Lemma.Fin.IsClassFunctionCharacter
open CategoryTheory
open scoped MonoidAlgebra
open MathlibExt.GroupTheory.ClassFunctionWanted

noncomputable section

universe u v

namespace FDRep

private def irrCharPairing {G : Type*} [Group G] [Finite G] (W : FDRep ℂ G) :
    (G → ℂ) →ₗ[ℂ] ℂ := by
  exact {
    toFun := fun f ↦ (Nat.card G : ℂ)⁻¹ * ∑ᶠ g, f g * W.character g⁻¹
    map_add' := by
      let _ := Fintype.ofFinite G
      intro f h
      simp only [finsum_eq_sum_of_fintype, Pi.add_apply, add_mul,
        Finset.sum_add_distrib, mul_add]
    map_smul' := by
      let _ := Fintype.ofFinite G
      intro c f
      simp only [finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      calc
        (Nat.card G : ℂ)⁻¹ * ∑ g, c * f g * W.character g⁻¹ =
            ∑ g, (Nat.card G : ℂ)⁻¹ * (c * f g * W.character g⁻¹) :=
          Finset.mul_sum _ _ _
        _ = ∑ g, c * ((Nat.card G : ℂ)⁻¹ * (f g * W.character g⁻¹)) := by
          apply Finset.sum_congr rfl
          intro g hg
          ring
        _ = c * ∑ g, (Nat.card G : ℂ)⁻¹ * (f g * W.character g⁻¹) :=
          (Finset.mul_sum _ _ _).symm
        _ = c * ((Nat.card G : ℂ)⁻¹ * ∑ g, f g * W.character g⁻¹) := by
          congr 1
          exact (Finset.mul_sum _ _ _).symm }

private noncomputable def irrCharOp {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : G → ℂ) :
    Module.End ℂ V :=
  ∑ᶠ g, f g • ρ g⁻¹

private noncomputable instance irrCharSmallMonoidAlgebra {G : Type*} [Finite G] :
    Small.{0} ℂ[G] :=
  (small_congr MonoidAlgebra.coeffEquiv).mpr inferInstance

private noncomputable def irrCharRegular {G : Type*} [Group G] [Finite G] :
    Representation ℂ G (Shrink.{0} ℂ[G]) :=
  (Shrink.linearEquiv ℂ ℂ[G]).symm.conjRingEquiv.toMonoidHom.comp
    (Representation.leftRegular ℂ G)

private noncomputable def irrCharModuleOp {G M : Type*} [Group G] [Finite G]
    [AddCommGroup M] [Module ℂ[G] M] [Module ℂ M] [IsScalarTower ℂ ℂ[G] M]
    (f : G → ℂ) : Module.End ℂ M :=
  ∑ᶠ g, f g • (Representation.ofModule' (k := ℂ) (G := G) M) g⁻¹
end FDRep
namespace MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted
end MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted
