import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import Instance.Data.Holor.Tensor.Part2
import Def.MeasureTheory.Integral.IntervalIntegral.Integrals.Part3
open Tensor


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

