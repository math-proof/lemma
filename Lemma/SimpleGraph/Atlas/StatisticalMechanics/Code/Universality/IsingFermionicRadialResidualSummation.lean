import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicRadialResidualSummation
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[finiteSum_le_harmonic_of_radialShellBoundAtScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicRadialResidualSummation.lean)
-/
@[path]
private lemma finiteSum_le_harmonic_of_radialShellBoundAtScale_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {scale shellCount : Nat}
  {C D : Real}
-- given
  (hscale : 0 < scale)
  (radius : alpha -> Nat)
  (f : alpha -> Real)
  (hC : 0 <= C)
  (hradius : forall a, radius a < shellCount)
  (hf : forall a, f a <= C / ((scale : Real) * ((radius a + 1 : Nat) : Real) ^ 2))
  (hshell : forall r, r < shellCount -> (((univ.filter (fun a => radius a = r)).card : Nat) : Real) <= D * ((r + 1 : Nat) : Real)) :
-- imply
  (∑ a, f a : Real) <= C * D * (harmonic shellCount : Real) / (scale : Real) := by
-- proof
  apply StatMech.Universality.finiteSum_le_harmonic_of_radialShellBoundAtScale scale shellCount hscale radius f C D hC hradius hf hshell

/--
[finiteSum_le_harmonic_of_radialShellBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicRadialResidualSummation.lean)
-/
@[path]
private lemma finiteSum_le_harmonic_of_radialShellBound_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {n : Nat}
  {C D : Real}
-- given
  (hn : 0 < n)
  (radius : alpha -> Nat)
  (f : alpha -> Real)
  (hC : 0 <= C)
  (hradius : forall a, radius a < n)
  (hf : forall a, f a <= C / ((n : Real) * ((radius a + 1 : Nat) : Real) ^ 2))
  (hshell : forall r, r < n -> (((univ.filter (fun a => radius a = r)).card : Nat) : Real) <= D * ((r + 1 : Nat) : Real)) :
-- imply
  (∑ a, f a : Real) <= C * D * (harmonic n : Real) / (n : Real) := by
-- proof
  apply StatMech.Universality.finiteSum_le_harmonic_of_radialShellBound n hn radius f C D hC hradius hf hshell

/--
[tendsto_harmonic_div_natCast_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicRadialResidualSummation.lean)
-/
@[path]
private lemma tendsto_harmonic_div_natCast_succ_eq :
-- imply
  Tendsto (fun n : Nat => (harmonic (n + 1) : Real) / ((n + 1 : Nat) : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.tendsto_harmonic_div_natCast_succ

/--
[tendsto_const_mul_harmonic_div_natCast_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicRadialResidualSummation.lean)
-/
@[path]
private lemma tendsto_const_mul_harmonic_div_natCast_succ_eq
  {C D : Real} :
-- imply
  Tendsto (fun n : Nat => C * D * (harmonic (n + 1) : Real) / ((n + 1 : Nat) : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.tendsto_const_mul_harmonic_div_natCast_succ C D

/--
[vertexSpatialTargetResidualPotential_le_harmonic_of_radialShellBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicRadialResidualSummation.lean)
-/
@[path]
private lemma vertexSpatialTargetResidualPotential_le_harmonic_of_radialShellBound_eq
  {n : Nat}
  {shellCount : Nat}
  {x : Option (FKIsingSquareFullVertexNode n)}
  {C D : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullVertexNode n) -> Real)
  (radius : Option (FKIsingSquareFullVertexNode n) -> Nat)
  (hC : 0 <= C)
  (hradius : forall z, radius z < shellCount)
  (hpoint : forall z, vertexSpatialTargetResidual n target z * vertexPointPoissonBarrier n z x <= C / ((n : Real) * ((radius z + 1 : Nat) : Real) ^ 2))
  (hshell : forall r, r < shellCount -> (((Finset.univ.filter (fun z => radius z = r)).card : Nat) : Real) <= D * ((r + 1 : Nat) : Real)) :
-- imply
  vertexSpatialTargetResidualPotential n target x <= C * D * (harmonic shellCount : Real) / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidualPotential_le_harmonic_of_radialShellBound n hn shellCount target x radius C D hC hradius hpoint hshell

/--
[faceSpatialTargetResidualPotential_le_harmonic_of_radialShellBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicRadialResidualSummation.lean)
-/
@[path]
private lemma faceSpatialTargetResidualPotential_le_harmonic_of_radialShellBound_eq
  {n : Nat}
  {shellCount : Nat}
  {x : Option (FKIsingSquareFullFaceNode n)}
  {C D : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullFaceNode n) -> Real)
  (radius : Option (FKIsingSquareFullFaceNode n) -> Nat)
  (hC : 0 <= C)
  (hradius : forall z, radius z < shellCount)
  (hpoint : forall z, faceSpatialTargetResidual n target z * facePointPoissonBarrier n z x <= C / ((n : Real) * ((radius z + 1 : Nat) : Real) ^ 2))
  (hshell : forall r, r < shellCount -> (((Finset.univ.filter (fun z => radius z = r)).card : Nat) : Real) <= D * ((r + 1 : Nat) : Real)) :
-- imply
  faceSpatialTargetResidualPotential n target x <= C * D * (harmonic shellCount : Real) / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidualPotential_le_harmonic_of_radialShellBound n hn shellCount target x radius C D hC hradius hpoint hshell


-- created on 2026-10-23
