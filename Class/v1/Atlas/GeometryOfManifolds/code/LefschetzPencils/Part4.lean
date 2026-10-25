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
import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- **Gompf's theorem (1998).**

If $f: M^4 \to \Sigma^2$ is a Lefschetz fibration with $[F] \neq 0 \in H_2(M,\mathbb{R})$,
then $M$ carries a symplectic form $\omega_M$ whose restriction to each generic fiber
is symplectic, exhibiting the fiber as a symplectic submanifold. -/
class IsBlowup
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_Mhat : ℕ → Type*} {VF_Mhat : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_Mhat : DifferentialFormSpace Ω_Mhat VF_Mhat]
    (S : SymplecticManifold Ω_M VF_M) : Prop where
  exists_blowdown :
    ∃ (blowdown : DFSMorphism Ω_Mhat VF_Mhat Ω_M VF_M)
      (numBlowups : ℕ) (_ : 0 < numBlowups)
      (exceptionalClass : Fin numBlowups → Ω_Mhat 2),

      (∀ j, inst_Mhat.d (exceptionalClass j) = 0) ∧


      (∀ j, ¬ ∃ (β : Ω_Mhat 1), inst_Mhat.d β = exceptionalClass j) ∧


      (∀ _j : Fin numBlowups,
        HasLocalQuadraticModel (inst_M := inst_Mhat) (inst_B2 := inst_M) blowdown)

/-- The differential-form space admits a **Lefschetz fibration to $S^2$**: there exist
form spaces for a 2-dimensional base $B$ and a fiber $F$, orientations on both
total space and base, a `LefschetzFibration` between them, and a symplectic 2-form
on $B$ which is closed, non-degenerate, and non-exact (modeling the $S^2$ symplectic
form). -/
class AdmitsLefschetzFibration
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] : Prop where
  exists_fibration :
    ∃ (Ω_B : ℕ → Type*) (VF_B : Type*) (inst_B : DifferentialFormSpace Ω_B VF_B)
      (Ω_F : ℕ → Type*) (VF_F : Type*) (inst_F : DifferentialFormSpace Ω_F VF_F)
      (_orientM : @IsOriented Ω VF inst) (_orientB : @IsOriented Ω_B VF_B inst_B)
      (_lf : @LefschetzFibration Ω VF Ω_B VF_B Ω_F VF_F inst inst_B inst_F _orientM _orientB),

      ∃ (ωB : Ω_B 2),
        inst_B.d ωB = 0 ∧
        Function.Injective (fun (X : VF_B) => inst_B.ι X ωB) ∧

        ¬ (∃ (β : Ω_B 1), inst_B.d β = ωB)


