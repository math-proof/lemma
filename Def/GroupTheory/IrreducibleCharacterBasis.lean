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
open CategoryTheory
open scoped MonoidAlgebra
open MathlibExt.GroupTheory.ClassFunctionWanted


noncomputable section

universe u v

namespace FDRep

def irrCharPairing {G : Type*} [Group G] [Finite G] (W : FDRep ℂ G) :
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

noncomputable def irrCharOp {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : G → ℂ) :
    Module.End ℂ V :=
  ∑ᶠ g, f g • ρ g⁻¹

end FDRep
end
