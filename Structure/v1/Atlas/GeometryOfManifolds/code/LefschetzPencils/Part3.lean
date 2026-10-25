/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- A **Lefschetz fibration** $f: M^4 \to \Sigma^2$ between oriented manifolds with a
finite set of isolated critical points, each locally modeled in oriented complex
coordinates as $\mathbb{C}^2 \to \mathbb{C}$, $(z_1, z_2) \mapsto z_1^2 + z_2^2$.

Carries:
- the map $f$,
- inclusion of a generic fiber,
- a finite list of critical points, and
- at each critical point, an instance of `HasLocalQuadraticModel`. -/
structure LefschetzFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [orientM : IsOriented Ω_M VF_M]
    [orientB : IsOriented Ω_B2 VF_B2] where
  f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2
  genericFiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M
  numCriticalPoints : ℕ
  dim_total_eq : orientM.dim = 4
  dim_base_eq : orientB.dim = 2
  hasLocalModel : ∀ (_ : Fin numCriticalPoints),
    HasLocalQuadraticModel (inst_M := inst_M) (inst_B2 := inst_B2) f

/-- A **vanishing cycle** of a Lefschetz fibration: a (codimension-one) cycle in a
generic fiber that collapses to a point at a designated critical point, encoded as
a morphism from a "cycle" form space into the fiber form space along with the
critical-point index. -/
structure VanishingCycle
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    {Ω_S : ℕ → Type*} {VF_S : Type*}
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [inst_S : DifferentialFormSpace Ω_S VF_S] where
  cycle : DFSMorphism Ω_S VF_S Ω_F VF_F
  criticalPointIndex : ℕ

/-- The **monodromy representation** of a Lefschetz fibration: for each singular fiber,
a Dehn twist of the generic fiber, together with its inverse, satisfying the
two-sided inverse axioms. -/
structure MonodromyRep
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_F : DifferentialFormSpace Ω_F VF_F] where
  numSingularFibers : ℕ
  dehnTwist : Fin numSingularFibers → DFSMorphism Ω_F VF_F Ω_F VF_F
  dehnTwistInv : Fin numSingularFibers → DFSMorphism Ω_F VF_F Ω_F VF_F
  left_inv : ∀ (j : Fin numSingularFibers) {p : ℕ} (α : Ω_F p),
    (dehnTwistInv j).pullback ((dehnTwist j).pullback α) = α
  right_inv : ∀ (j : Fin numSingularFibers) {p : ℕ} (α : Ω_F p),
    (dehnTwist j).pullback ((dehnTwistInv j).pullback α) = α


/-- The hypothesis "$[F] \neq 0 \in H_2(M, \mathbb{R})$" of Gompf's theorem, expressed
dually: there exists a closed 2-form $\eta$ on $M$ whose restriction to the generic
fiber is non-zero (so $[F]$ pairs non-trivially with the cohomology class $[\eta]$). -/
structure FiberClassNonzero
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [IsOriented Ω_M VF_M] [IsOriented Ω_B2 VF_B2]
    (lf : LefschetzFibration (inst_M := inst_M) (inst_B2 := inst_B2) (inst_F := inst_F)) : Prop where
  exists_pairing_witness : ∃ (η : Ω_M 2),
    inst_M.d η = 0 ∧ lf.genericFiberInclusion.pullback η ≠ 0


