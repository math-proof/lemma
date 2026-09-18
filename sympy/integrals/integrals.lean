import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import torch.Tensor
open Tensor


inductive LSpace | mk

def ℒ : LSpace := .mk

instance : HPow LSpace ℕ (ℝ → ℝ → Set (ℝ → ℝ)) := ⟨fun _ _ a b => {f | IntervalIntegrable f MeasureTheory.volume a b}⟩

notation "ℒ¹" => (ℒ ^ 1 : ℝ → ℝ → Set (ℝ → ℝ))


/-- `Tensor α s` is equivalent to `List.Vector α s.prod` via `Tensor.data`. -/
def Tensor.equivData (α : Type*) (s : List ℕ) : Tensor α s ≃ List.Vector α s.prod :=
  ⟨Tensor.data, Tensor.mk, fun _ => rfl, fun _ => rfl⟩

/-- `Tensor α s` is equivalent to `Fin s.prod → α`. -/
def Tensor.equivFinArrow (α : Type*) (s : List ℕ) : Tensor α s ≃ (Fin s.prod → α) :=
  (Tensor.equivData α s).trans (Equiv.vectorEquivFin α s.prod)

/-- Scalar multiplication on `Tensor α s` via elementwise multiplication. -/
instance [Mul α] : SMul α (Tensor α s) where
  smul r X := ⟨X.data.map (r * ·)⟩

/-- `Tensor α s` as an `AddMonoidHom` to `Fin s.prod → α` (using natural `Add`/`Zero`). -/
def Tensor.toAddMonoidHom (α : Type*) (s : List ℕ) [AddMonoid α] :
    Tensor α s →+ (Fin s.prod → α) where
  toFun := Tensor.equivFinArrow α s
  map_zero' := by
    funext j
    simp only [Tensor.equivFinArrow, Tensor.equivData, Equiv.vectorEquivFin,
      Equiv.trans_apply, Equiv.coe_fn_mk]
    exact List.Vector.get_replicate 0 j
  map_add' := fun X Y => by
    funext j
    simp only [Tensor.equivFinArrow, Tensor.equivData, Equiv.vectorEquivFin,
      Equiv.trans_apply, Equiv.coe_fn_mk]
    show (X.data.map₂ HAdd.hAdd Y.data).get j = X.data.get j + Y.data.get j
    rw [List.Vector.get_map₂]

instance [NormedAddCommGroup α] : NormedAddCommGroup (Tensor α s) :=
  NormedAddCommGroup.induced _ _ (Tensor.toAddMonoidHom α s)
    (Tensor.equivFinArrow α s).injective

/-- `Module α (Tensor α s)` instance using natural `AddCommMonoid` and direct `SMul`. -/
instance [Semiring α] : Module α (Tensor α s) where
  smul_zero := by
    intro r
    apply Eq.of.EqDataS
    ext i
    show ((0 : Tensor α s).data.map (r * ·)).get i = ((0 : Tensor α s).data).get i
    rw [List.Vector.get_map, Tensor.EqData0'0, Vector.Zero.eq.Replicate,
        List.Vector.get_replicate]
    apply mul_zero
  smul_add := by
    intro r x y
    apply Eq.of.EqDataS
    ext i
    show ((x.data.map₂ HAdd.hAdd y.data).map (r * ·)).get i =
      ((x.data.map (r * ·)).map₂ HAdd.hAdd (y.data.map (r * ·))).get i
    rw [List.Vector.get_map, List.Vector.get_map₂, List.Vector.get_map₂,
        List.Vector.get_map, List.Vector.get_map]
    apply left_distrib
  add_smul := by
    intro r s x
    apply Eq.of.EqDataS
    ext i
    show (x.data.map ((r + s) * ·)).get i =
      ((x.data.map (r * ·)).map₂ HAdd.hAdd (x.data.map (s * ·))).get i
    rw [List.Vector.get_map, List.Vector.get_map₂,
        List.Vector.get_map, List.Vector.get_map]
    apply add_mul
  mul_smul := by
    intro r s x
    apply Eq.of.EqDataS
    ext i
    show (x.data.map ((r * s) * ·)).get i =
      ((x.data.map (s * ·)).map (r * ·)).get i
    rw [List.Vector.get_map, List.Vector.get_map, List.Vector.get_map]
    apply mul_assoc
  one_smul := by
    intro x
    apply Eq.of.EqDataS
    ext i
    show (x.data.map (1 * ·)).get i = x.data.get i
    rw [List.Vector.get_map]
    apply one_mul
  zero_smul := by
    intro x
    apply Eq.of.EqDataS
    ext i
    show (x.data.map (0 * ·)).get i = ((0 : Tensor α s).data).get i
    rw [List.Vector.get_map, Tensor.EqData0'0, Vector.Zero.eq.Replicate,
        List.Vector.get_replicate]
    apply zero_mul

/-- `NormedSpace ℝ` for `Tensor ℝ s` using the natural `Module ℝ` instance. -/
noncomputable instance : NormedSpace ℝ (Tensor ℝ s) where
  norm_smul_le r X := by
    show ‖(Tensor.toAddMonoidHom ℝ s) (r • X)‖ ≤ ‖r‖ * ‖(Tensor.toAddMonoidHom ℝ s) X‖
    have key : (Tensor.toAddMonoidHom ℝ s) (r • X) = r • (Tensor.toAddMonoidHom ℝ s) X := by
      funext j
      show (X.data.map (r * ·)).get j = r * (X.data.get j)
      rw [List.Vector.get_map]
    rw [key]
    exact norm_smul_le r ((Tensor.toAddMonoidHom ℝ s) X)

/-- Transport `CompleteSpace` from `Fin s.prod → α` to `Tensor α s`. -/
instance [NormedAddCommGroup α] [CompleteSpace α] : CompleteSpace (Tensor α s) := by
  have he : Isometry (Tensor.equivFinArrow α s : Tensor α s → Fin s.prod → α) :=
    PseudoMetricSpace.isometry_induced _
  exact (completeSpace_congr he.isUniformEmbedding).mpr inferInstance

/-- `Tensor α s` is linearly equivalent to `Fin s.prod → α`. -/
def Tensor.equivFinArrowL (α : Type*) (s : List ℕ) [Semiring α] :
    Tensor α s ≃ₗ[α] (Fin s.prod → α) where
  toFun := Tensor.equivFinArrow α s
  invFun := (Tensor.equivFinArrow α s).symm
  left_inv := (Tensor.equivFinArrow α s).left_inv
  right_inv := (Tensor.equivFinArrow α s).right_inv
  map_add' := (Tensor.toAddMonoidHom α s).map_add
  map_smul' := fun r X => by
    funext j
    show (X.data.map (r * ·)).get j = r * (X.data.get j)
    rw [List.Vector.get_map]

/-- `Tensor ℝ s` is finite-dimensional over `ℝ` (via `equivFinArrowL`). -/
instance : FiniteDimensional ℝ (Tensor ℝ s) :=
  FiniteDimensional.of_injective
    (Tensor.equivFinArrowL ℝ s).toLinearMap
    (Tensor.equivFinArrow ℝ s).injective
