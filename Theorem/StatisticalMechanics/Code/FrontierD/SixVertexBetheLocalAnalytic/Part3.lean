/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheResidualGraph_fderiv_injective_of_rootJacobian
    {N n : Nat} {c : Real} (hc : 2 < c) {p : Fin n → Real}
    (hjac : Function.Injective (sixVertexBetheRootJacobian N n c p)) :
    Function.Injective
      (fderiv Real (sixVertexBetheResidualGraph N n) (c, p)) := by
  let H := sixVertexBetheResidualGraph N n
  let L := fderiv Real H (c, p)
  let J := sixVertexBetheRootJacobian N n c p
  have hH : HasFDerivAt H L (c, p) :=
    (analyticAt_sixVertexBetheResidualGraph N n (c, p) hc).hasStrictFDerivAt.hasFDerivAt
  let incl : (Fin n → Real) →L[Real]
      (Real × (Fin n → Real)) :=
    (0 : (Fin n → Real) →L[Real] Real).prod
      (ContinuousLinearMap.id Real (Fin n → Real))
  have hincl : HasFDerivAt (fun q : Fin n → Real => (c, q)) incl p :=
    (hasFDerivAt_const c p).prodMk (hasFDerivAt_id p)
  have hcomp : HasFDerivAt
      (fun q : Fin n → Real => H (c, q)) (L.comp incl) p :=
    hH.comp p hincl
  have hres : HasFDerivAt
      (fun q : Fin n → Real =>
        fun j => sixVertexBetheResidual c N n q j) J p := by
    exact (analyticAt_sixVertexBetheResidual_family N n (c, p) hc).comp
      (x := p) (f := fun q : Fin n → Real => (c, q))
      (analyticAt_const.prod analyticAt_id) |>.hasStrictFDerivAt.hasFDerivAt
  let direct : (Fin n → Real) →L[Real]
      (Real × (Fin n → Real)) :=
    (0 : (Fin n → Real) →L[Real] Real).prod J
  have hdirect : HasFDerivAt
      (fun q : Fin n → Real => H (c, q)) direct p := by
    exact (hasFDerivAt_const c p).prodMk hres
  have hderiv : L.comp incl = direct := hcomp.unique hdirect
  intro z w hzw
  let u := z - w
  have hu : L u = 0 := by
    dsimp [u, L]
    rw [map_sub, hzw, sub_self]
  have hfst : u.1 = 0 := by
    have hproj : HasFDerivAt (fun q : Real × (Fin n → Real) => q.1)
        (ContinuousLinearMap.fst Real Real (Fin n → Real)) (c, p) :=
      (ContinuousLinearMap.fst Real Real (Fin n → Real)).hasFDerivAt
    have hcompFst : HasFDerivAt
        (fun q : Real × (Fin n → Real) => q.1)
        ((ContinuousLinearMap.fst Real Real (Fin n → Real)).comp L)
        (c, p) := by
      simpa [H, sixVertexBetheResidualGraph] using
        ((ContinuousLinearMap.fst Real Real (Fin n → Real)).hasFDerivAt.comp
          (c, p) hH)
    have hfstL :
        (ContinuousLinearMap.fst Real Real (Fin n → Real)).comp L =
          ContinuousLinearMap.fst Real Real (Fin n → Real) :=
      hcompFst.unique hproj
    have h := congrArg
      (fun T : (Real × (Fin n → Real)) →L[Real] Real => T u) hfstL
    simpa [hu] using h.symm
  have hupair : u = (0, u.2) := Prod.ext hfst rfl
  have hJzero : J u.2 = 0 := by
    have happly := congrArg
      (fun T : (Fin n → Real) →L[Real]
        (Real × (Fin n → Real)) => T u.2) hderiv
    have hLzero : L (incl u.2) = 0 := by
      rw [show incl u.2 = u by
        rw [hupair]
        rfl]
      exact hu
    simpa [hLzero, direct] using (congrArg Prod.snd happly).symm
  have hu2 : u.2 = 0 := hjac (by simpa using hJzero)
  have hsub : z - w = 0 := by
    change u = 0
    exact Prod.ext hfst hu2
  exact sub_eq_zero.mp hsub


theorem isOpen_sixVertexStrictRootTuples (n : Nat) :
    IsOpen {p : Fin n → Real | StrictMono p} := by
  rw [show {p : Fin n → Real | StrictMono p} =
      ⋂ i, ⋂ j, ⋂ (_h : i < j), {p | p i < p j} by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact Iff.rfl]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ =>
      isOpen_lt (continuous_apply i) (continuous_apply j)


theorem isOpen_sixVertexRootsInOpenInterval (n : Nat) :
    IsOpen {p : Fin n → Real | SixVertexRootsInOpenInterval p} := by
  rw [show {p : Fin n → Real | SixVertexRootsInOpenInterval p} =
      ⋂ j, {p | -Real.pi < p j ∧ p j < Real.pi} by
    ext p
    simp [SixVertexRootsInOpenInterval]]
  exact isOpen_iInter_of_finite fun j =>
    (isOpen_lt continuous_const (continuous_apply j)).inter
      (isOpen_lt (continuous_apply j) continuous_const)


theorem isOpen_sixVertexNonsymmetricOpenRootDomain (n : Nat) :
    IsOpen {p : Fin n → Real |
      StrictMono p ∧ SixVertexRootsInOpenInterval p} :=
  (isOpen_sixVertexStrictRootTuples n).inter
    (isOpen_sixVertexRootsInOpenInterval n)


end
end StatMech.FrontierD
