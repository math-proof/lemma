/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.HodgeTheory
import Mathlib.Geometry.Manifold.MFDeriv.Basic


set_option autoImplicit false

open DifferentialFormSpace


/-- A tangent-bundle splitting compatible with a 2-form $\eta$.

Encodes a decomposition $TM = V \oplus H$ into vertical and horizontal subbundles via
projections `projV` and `projH`. Contraction with $\eta$ (and with any $(p+1)$-form)
distributes over the splitting, the projections are idempotent and mutually
annihilating, and the splitting is "orthogonal" with respect to $\eta$ in the sense
that $\iota_{V Y} \iota_{H X} \eta = 0$. -/
class TangentSplitting
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η : Ω 2) where
  projV : VF → VF
  projH : VF → VF
  decompose : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι X α = inst.ι (projV X) α + inst.ι (projH X) α
  projV_idem : ∀ (X : VF), projV (projV X) = projV X
  projH_idem : ∀ (X : VF), projH (projH X) = projH X
  complement_VH : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (projV (projH X)) α = 0
  complement_HV : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (projH (projV X)) α = 0
  orthogonal : ∀ (X Y : VF),
    inst.ι (projV Y) (inst.ι (projH X) η) = 0


/-- A **symplectic fibration** $f: M \to B$ with generic fiber $(F, \omega_F)$ symplectic.

Bundles together the projection `f`, the fiber inclusion, the symplectic form on the
fiber, and an open cover with local trivializations whose transition maps preserve
$\omega_F$. The cocycle and inverse axioms ensure the data really comes from a
fiber-bundle structure with structure group $\mathrm{Symp}(F,\omega_F)$. -/
structure SymplecticFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F] where
  f : DFSMorphism Ω_M VF_M Ω_B VF_B
  fiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M
  fiberSymplectic : SymplecticManifold Ω_F VF_F
  CoverIdx : Type
  coverNonempty : Nonempty CoverIdx
  localTriv : CoverIdx → DFSMorphism Ω_F VF_F Ω_M VF_M
  localTriv_symplectic : ∀ (i : CoverIdx) (η : Ω_M 2),
    fiberInclusion.pullback η = fiberSymplectic.ω →
    (localTriv i).pullback η = fiberSymplectic.ω
  transitionMap : CoverIdx → CoverIdx → DFSMorphism Ω_F VF_F Ω_F VF_F
  transition_from_localTriv : ∀ (i j : CoverIdx) {p : ℕ} (α : Ω_M p),
    (localTriv i).pullback α =
    (transitionMap i j).pullback ((localTriv j).pullback α)
  transition_preserves_symplectic : ∀ (i j : CoverIdx),
    (transitionMap i j).pullback fiberSymplectic.ω = fiberSymplectic.ω
  transition_inverse : ∀ (i j : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap i j).pullback ((transitionMap j i).pullback α) = α
  transition_cocycle : ∀ (i j k : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap j k).pullback ((transitionMap i j).pullback α) =
    (transitionMap i k).pullback α
  transition_diagonal : ∀ (i : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap i i).pullback α = α
  fiber_pullback_base_zero_general :
    ∀ {p : ℕ} (α : Ω_B (p + 1)),
    fiberInclusion.pullback (f.pullback α) = 0
  fiberInclusion_eq_localTriv :
    ∃ (i : CoverIdx), ∀ {p : ℕ} (α : Ω_M p),
      fiberInclusion.pullback α = (localTriv i).pullback α
  localTriv_surjective : ∀ (i : CoverIdx) {p : ℕ} (β : Ω_F p),
    ∃ (γ : Ω_M p), (localTriv i).pullback γ = β


/-- Tangent-bundle data for a symplectic fibration adapted to a closed 2-form $\tilde\eta$
that restricts to the fiber symplectic form $\omega_F$.

Packages a `TangentSplitting` for $\tilde\eta$ together with a vertical restriction
map $VF_M \to VF_F$, with axioms saying the vertical part kills base-pulled forms,
restriction is compatible with contraction by $\tilde\eta$, the restriction is
injective on verticals, and a non-degeneracy criterion in the horizontal direction
detected by the base symplectic form. -/
structure FibrationTangentBundle
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
    (η_tilde : Ω_M 2)
    (h_closed : inst_M.d η_tilde = 0)
    (h_fiber : fib.fiberInclusion.pullback η_tilde = fib.fiberSymplectic.ω) where
  splitting : @TangentSplitting _ _ inst_M η_tilde
  restrictV : VF_M → VF_F
  vertical_kills_base : ∀ (X : VF_M) {p : ℕ} (β : Ω_B (p + 1)),
    inst_M.ι (splitting.projV X) (fib.f.pullback β) = 0
  restrictV_compat : ∀ (X : VF_M),
    fib.fiberInclusion.pullback (inst_M.ι (splitting.projV X) η_tilde) =
    inst_F.ι (restrictV (splitting.projV X)) (fib.fiberInclusion.pullback η_tilde)
  restrictV_inj : ∀ (X Y : VF_M),
    restrictV (splitting.projV X) = restrictV (splitting.projV Y) →
    splitting.projV X = splitting.projV Y
  horizontal_nondegen : ∀ (baseSymplectic : SymplecticManifold Ω_B VF_B) (X Y : VF_M),
    splitting.projV X = splitting.projV Y →
    inst_M.ι X (fib.f.pullback baseSymplectic.ω) =
    inst_M.ι Y (fib.f.pullback baseSymplectic.ω) → X = Y


/-- Auxiliary class bundling the data needed for Thurston's construction:
a tangent splitting compatible with $\eta$, vanishing of the base pullback on
vertical vectors, vertical non-degeneracy of $\eta$, and (for sufficiently large $k$)
non-degeneracy of $\eta + k\, f^*\omega_B$. -/
class ThurstonSplittingData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_B : ℕ → Type*} {VF_B : Type*} [inst_B : DifferentialFormSpace Ω_B VF_B]
    {Ω_F : ℕ → Type*} {VF_F : Type*} [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst) (inst_B := inst_B) (inst_F := inst_F))
    (baseSymplectic : SymplecticManifold Ω_B VF_B)
    (η : Ω 2)
    (h_η_restricts : fib.fiberInclusion.pullback η = fib.fiberSymplectic.ω)
    extends TangentSplitting (inst := inst) η where
  pullback_vanishes : ∀ (X : VF),
    inst.ι (projV X) (fib.f.pullback baseSymplectic.ω) = 0
  eta_nondegen_vertical : ∀ (X Y : VF),
    inst.ι (projV X) η = inst.ι (projV Y) η → projV X = projV Y
  horiz_nondegen : ∃ (k₀ : ℕ), ∀ (k : ℕ), k₀ ≤ k →
    ∀ (X Y : VF), projV X = projV Y →
      inst.ι X (η + (k : ℝ) • fib.f.pullback baseSymplectic.ω) =
      inst.ι Y (η + (k : ℝ) • fib.f.pullback baseSymplectic.ω) → X = Y


/-- Local complex coordinates $(z_1, z_2)$ on a 2-complex-dimensional patch:
two 0-forms $z_1, z_2$ with their differentials $dz_1, dz_2$, where $dz_1 \neq 0$
and $dz_2$ is not a real multiple of $dz_1$ (so $\{dz_1, dz_2\}$ are linearly
independent). Used to express the Lefschetz local model $(z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
structure HasComplexCoords₂
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  z₁ : Ω 0
  z₂ : Ω 0
  dz₁ : Ω 1
  dz₂ : Ω 1
  dz₁_eq : inst.d z₁ = dz₁
  dz₂_eq : inst.d z₂ = dz₂
  dz₁_ne_zero : dz₁ ≠ 0
  dz₂_indep : ∀ (r : ℝ), dz₂ ≠ r • dz₁

/-- A single local complex coordinate $w$ with non-zero differential $dw$, used as the
target coordinate for the standard Lefschetz model $w = z_1^2 + z_2^2$. -/
structure HasComplexCoord₁
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  w : Ω 0
  dw : Ω 1
  dw_eq : inst.d w = dw
  dw_ne_zero : dw ≠ 0

/-- The local model map $q: \mathbb{C}^2 \to \mathbb{C}$ at a Lefschetz critical point,
characterized in coordinates by the formula $q^*(w) = z_1^2 + z_2^2$. -/
structure IsStandardQuadraticMap
    {Ω_src : ℕ → Type*} {VF_src : Type*}
    {Ω_tgt : ℕ → Type*} {VF_tgt : Type*}
    [inst_src : DifferentialFormSpace Ω_src VF_src]
    [inst_tgt : DifferentialFormSpace Ω_tgt VF_tgt]
    (q : DFSMorphism Ω_src VF_src Ω_tgt VF_tgt)
    (coords_src : HasComplexCoords₂ Ω_src VF_src)
    (coord_tgt : HasComplexCoord₁ Ω_tgt VF_tgt) where
  q_formula : q.pullback coord_tgt.w =
    inst_src.fMul coords_src.z₁ coords_src.z₁ +
    inst_src.fMul coords_src.z₂ coords_src.z₂


/-- A map $f: M^4 \to B^2$ **has the standard Lefschetz local quadratic model** at a
critical point: there exist local source and target charts and a model map $q$ such
that $f$ pulls back to $q$ on the charted domain, $q$ has a critical point (degenerate
contraction with some non-zero 1-form), a non-degenerate symplectic 2-form
pulls back to a non-degenerate form upstairs, and the pair is the standard quadratic
map $(z_1, z_2) \mapsto z_1^2 + z_2^2$ in suitable complex coordinates. -/
def HasLocalQuadraticModel
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    (f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2) : Prop :=


  ∃ (Ω_loc_src : ℕ → Type) (VF_loc_src : Type)
    (inst_loc_src : DifferentialFormSpace Ω_loc_src VF_loc_src)
    (Ω_loc_tgt : ℕ → Type) (VF_loc_tgt : Type)
    (inst_loc_tgt : DifferentialFormSpace Ω_loc_tgt VF_loc_tgt)

    (q : @DFSMorphism Ω_loc_src VF_loc_src Ω_loc_tgt VF_loc_tgt inst_loc_src inst_loc_tgt)

    (chartSource : @DFSMorphism Ω_loc_src VF_loc_src Ω_M VF_M inst_loc_src inst_M)

    (chartTarget : @DFSMorphism Ω_loc_tgt VF_loc_tgt Ω_B2 VF_B2 inst_loc_tgt inst_B2),

    (∀ {p : ℕ} (α : Ω_B2 p),
      chartSource.pullback (f.pullback α) = q.pullback (chartTarget.pullback α)) ∧


    (∃ (α : Ω_loc_tgt 1), α ≠ 0 ∧
      ¬ Function.Injective (fun (v : VF_loc_src) =>
        inst_loc_src.ι v (q.pullback α))) ∧


    (∃ (ω_tgt : Ω_loc_tgt 2),

      Function.Injective (fun (v : VF_loc_tgt) =>
        inst_loc_tgt.ι v ω_tgt) ∧

      Function.Injective (fun (v : VF_loc_src) =>
        inst_loc_src.ι v (q.pullback ω_tgt))) ∧


    (∃ (coords_src : @HasComplexCoords₂ Ω_loc_src VF_loc_src inst_loc_src)
       (coord_tgt : @HasComplexCoord₁ Ω_loc_tgt VF_loc_tgt inst_loc_tgt),
       @IsStandardQuadraticMap Ω_loc_src VF_loc_src Ω_loc_tgt VF_loc_tgt
         inst_loc_src inst_loc_tgt q coords_src coord_tgt)

/-- An orientation on a differential-form space: a fixed top-degree dimension,
a nowhere-vanishing closed volume form. -/
class IsOriented
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  dim : ℕ
  volumeForm : Ω dim
  volumeForm_ne_zero : volumeForm ≠ 0
  volumeForm_closed : inst.d volumeForm = 0


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


/-- **Donaldson's theorem on Lefschetz pencils.**

For any compact symplectic 4-manifold $(M^4, \omega)$, after blowing up finitely many
points the resulting manifold $\hat M$ admits a Lefschetz fibration to $S^2$. -/
structure FiberSum.DFS
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    {Ω_Q : ℕ → Type*} {VF_Q : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst_Q : DifferentialFormSpace Ω_Q VF_Q]
    [dim_M₁ : SymplecticManifoldDim Ω₁ VF₁]
    [dim_M₂ : SymplecticManifoldDim Ω₂ VF₂]
    [dim_Q : SymplecticManifoldDim Ω_Q VF_Q]
    [IsCompactManifold Ω_Q VF_Q] where
  M₁ : SymplecticManifold Ω₁ VF₁
  M₂ : SymplecticManifold Ω₂ VF₂
  Q : SymplecticManifold Ω_Q VF_Q
  ι₁ : DFSMorphism Ω_Q VF_Q Ω₁ VF₁
  ι₂ : DFSMorphism Ω_Q VF_Q Ω₂ VF₂
  ι₁_symplectic : ι₁.pullback M₁.ω = Q.ω
  ι₂_symplectic : ι₂.pullback M₂.ω = Q.ω
  codim_two_M₁ : dim_Q.n + 1 = dim_M₁.n
  codim_two_M₂ : dim_Q.n + 1 = dim_M₂.n
  normalBundleTriv_M₁ : ∃ (η : Ω₁ 2),
    inst₁.d η = 0 ∧ ι₁.pullback η = 0 ∧ η ≠ 0
  normalBundleTriv_M₂ : ∃ (η : Ω₂ 2),
    inst₂.d η = 0 ∧ ι₂.pullback η = 0 ∧ η ≠ 0


/-- **Symplectic sum (existence).**

Given two symplectic manifolds $(M_1, \omega_1)$, $(M_2, \omega_2)$ and a common
codimension-2 symplectic submanifold $Q$ with inclusions pulling back the ambient
symplectic forms to $\omega_Q$, there exists a new symplectic manifold $R$ with
embeddings $j_k : M_k \hookrightarrow R$ such that $j_k^*\omega_R = \omega_k$.
Moreover $R$ admits a closed 2-form $\eta$ that is exact on each $M_k$ but not on
$R$, witnessing a new cohomology class created by the sum. -/
class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  has_finite_presentation : ∃ (n m : ℕ) (f : FreeGroup (Fin n) →* G),
    Function.Surjective f ∧
    ∃ (rels : Fin m → FreeGroup (Fin n)),
      MonoidHom.ker f = Subgroup.normalClosure (Set.range rels)

/-- The group $G$ is the fundamental group $\pi_1$ of the compact symplectic 4-manifold
$S$: $S$ is finitely presented, admits a compatible almost complex structure, and
there is a group isomorphism $\pi_1(S) \cong G$. -/
class IsFundGroupOfSymplectic4Mfd
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (G : Type*) [Group G] where
  fp : IsFinitelyPresented G
  has_acs : ∃ (J : AlmostComplexStr (inst := inst)), IsCompatibleACS S J
  π₁ : Type*
  grp_π₁ : Group π₁
  iso : @MulEquiv π₁ G grp_π₁.toMul _


/-- **Gompf's realization theorem for fundamental groups.**

Every finitely presented group $G$ arises as the fundamental group $\pi_1(S)$ of some
compact symplectic 4-manifold $S$. -/
structure HasHandlebodyDecomposition
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] : Prop where
  handle_data : ∃ (n₀ _n₁ n₂ _n₃ n₄ : ℕ),
    n₀ = 1 ∧ n₄ = 1 ∧ 0 < n₂

/-- Carrier for an Euler characteristic value $\chi \in \mathbb{Z}$. -/
structure HasEulerCharacteristic
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  euler : ℤ


/-- A pullback morphism $\varphi$ is **$\omega$-tame** if the pulled-back form
$\varphi^*\omega$ is non-degenerate on contraction. -/
class IsOmegaTame
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (φ : DFSMorphism Ω VF Ω VF) : Prop where
  taming_nondeg : Function.Injective (fun (v : VF) => inst.ι v (φ.pullback S.ω))

/-- A **symplectic branched covering**: a symplectic target $(Y, \omega_Y)$, a covering
map $f: X \to Y$, and an integer degree $\geq 1$. -/
structure SymplecticBranchedCovering
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y] where
  target : SymplecticManifold Ω_Y VF_Y
  f : DFSMorphism Ω_X VF_X Ω_Y VF_Y
  degree : ℕ
  degree_pos : 0 < degree


/-- Data for the **perturbation step** in symplectifying a branched cover: a closed
auxiliary 2-form $\alpha$ and parameter $\varepsilon \neq 0$ together with a
tangent splitting whose vertical kernel is annihilated by $\eta$ (the pullback
of the base symplectic form), $\alpha$ is non-degenerate on the kernel, and
$\eta + \varepsilon\alpha$ is non-degenerate on horizontal vectors. -/
class BranchedCoverPerturbationData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η α : Ω 2) (ε : ℝ)
    extends TangentSplitting (inst := inst) α where
  ε_ne_zero : ε ≠ 0
  pullback_vanishes_on_K : ∀ (X : VF), inst.ι (projV X) η = 0
  alpha_nondeg_on_K : ∀ (X Y : VF),
    inst.ι (projV X) α = inst.ι (projV Y) α → projV X = projV Y
  complement_nondeg : ∀ (X Y : VF), projV X = projV Y →
    inst.ι X (η + ε • α) = inst.ι Y (η + ε • α) → X = Y
  alpha_closed : inst.d α = 0


/-- Data for the **adjunction formula** for a symplectic surface inside a 4-manifold:
the genus $g$, self-intersection $[\Sigma]\cdot[\Sigma]$, the value $\langle c_1, [\Sigma]\rangle$,
the first Chern numbers of the tangent and normal bundles, and the relations
- $c_1(T\Sigma) = 2 - 2g$ (Gauss-Bonnet),
- $c_1(N\Sigma) = [\Sigma]\cdot[\Sigma]$ (normal-bundle degree),
- $\langle c_1, [\Sigma]\rangle = c_1(T\Sigma) + c_1(N\Sigma)$ (splitting of $c_1(TM)|_\Sigma$). -/
structure HasAdjunctionData
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  genus : ℕ
  selfIntersection : ℤ
  c₁_eval : ℤ
  chern_tangent : ℤ
  chern_normal : ℤ
  gauss_bonnet_eq : chern_tangent = 2 - 2 * (genus : ℤ)
  normal_bundle_degree_eq : chern_normal = selfIntersection
  chern_split_eq : c₁_eval = chern_tangent + chern_normal


/-- Data for the **ramification locus** $R \subset X$ of a symplectic branched cover
$f: X \to Y$ and its image $D \subset Y$ (the branch divisor): inclusions $R
\hookrightarrow X$ and $D \hookrightarrow Y$, the restricted map $f|_R: R \to D$,
the property that $f^*\omega_Y$ degenerates along $R$, and the factorization
$f \circ \mathrm{incl}_R = \mathrm{incl}_D \circ (f|_R)$. -/
structure RamificationData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y]
    (bc : SymplecticBranchedCovering (inst_X := inst_X) (inst_Y := inst_Y)) where
  Ω_R : ℕ → Type*
  VF_R : Type*
  [inst_R : DifferentialFormSpace Ω_R VF_R]
  Ω_D : ℕ → Type*
  VF_D : Type*
  [inst_D : DifferentialFormSpace Ω_D VF_D]
  inclR : @DFSMorphism Ω_R VF_R Ω_X VF_X inst_R inst_X
  inclD : @DFSMorphism Ω_D VF_D Ω_Y VF_Y inst_D inst_Y
  fRestrict : @DFSMorphism Ω_R VF_R Ω_D VF_D inst_R inst_D
  pullback_degenerate_on_R :
    ¬ Function.Injective (fun (v : VF_R) =>
        inst_R.ι v (inclR.pullback (bc.f.pullback bc.target.ω)))
  factorization : ∀ {p : ℕ} (α : Ω_Y p),
    inclR.pullback (bc.f.pullback α) = fRestrict.pullback (inclD.pullback α)


/-- A **symplectic form on a manifold $M$** in the manifold-with-corners formalism:
half the dimension, a skew-symmetric non-degenerate bilinear form on the model
space $E$. -/
structure ManifoldSymplecticForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ⊤ M] where
  halfDim : ℕ
  form : E →L[ℝ] E →L[ℝ] ℝ
  skew : ∀ (v w : E), form v w = -(form w v)
  nondegenerate : Function.Injective form


/-- **Symplectic fiber-sum data** in the manifold-with-corners formalism: two
symplectic manifolds $M_1, M_2$ with a common codimension-2 submanifold $Q$,
smooth injective embeddings $\iota_j: Q \hookrightarrow M_j$, matching dimensions,
and chosen trivializations of the normal $\mathbb R^2$-bundles of $Q$ in $M_1$
and $M_2$ along the zero section. -/
structure FiberSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M₁ M₂ Q : Type*)
    [TopologicalSpace M₁] [ChartedSpace H M₁] [IsManifold I ⊤ M₁]
    [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ⊤ M₂]
    [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ⊤ Q] where
  ι₁ : Q → M₁
  ι₂ : Q → M₂
  ι₁_injective : Function.Injective ι₁
  ι₂_injective : Function.Injective ι₂
  ι₁_smooth : MDifferentiable I I ι₁
  ι₂_smooth : MDifferentiable I I ι₂
  symp₁ : ManifoldSymplecticForm I M₁
  symp₂ : ManifoldSymplecticForm I M₂
  sympQ : ManifoldSymplecticForm I Q
  codim_two₁ : sympQ.halfDim + 1 = symp₁.halfDim
  codim_two₂ : sympQ.halfDim + 1 = symp₂.halfDim
  normalBundleTriv₁ : ∃ (U₁ : Set M₁) (φ₁ : U₁ → Q × (Fin 2 → ℝ)),
    Function.Bijective φ₁ ∧

    (∀ q : Q, ∃ h : ι₁ q ∈ U₁, φ₁ ⟨ι₁ q, h⟩ = (q, 0))
  normalBundleTriv₂ : ∃ (U₂ : Set M₂) (φ₂ : U₂ → Q × (Fin 2 → ℝ)),
    Function.Bijective φ₂ ∧
    (∀ q : Q, ∃ h : ι₂ q ∈ U₂, φ₂ ⟨ι₂ q, h⟩ = (q, 0))

/-- **Symplectic sum existence (manifold formulation).**

Given symplectic fiber-sum data $(M_1, M_2, Q)$ in the manifold-with-corners
formalism, there exists a smooth manifold $R$ carrying a symplectic form whose
half-dimension matches that of $M_1$. -/
structure LefschetzPencil.Mfld
    {E₄ : Type*} [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
    {H₄ : Type*} [TopologicalSpace H₄]
    (I₄ : ModelWithCorners ℝ E₄ H₄)
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    (I₂ : ModelWithCorners ℝ E₂ H₂)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H₄ M] [IsManifold I₄ ⊤ M]
    (B₂ : Type*) [TopologicalSpace B₂] [ChartedSpace H₂ B₂] [IsManifold I₂ ⊤ B₂]
    where
  f : M → B₂
  numCriticalPoints : ℕ
  criticalPoints : Fin numCriticalPoints → M
  smooth_away : ∀ x : M, (∀ i, x ≠ criticalPoints i) →
    MDifferentiableAt I₄ I₂ f x
  deriv_zero_at_crit : ∀ i : Fin numCriticalPoints,
    mfderiv I₄ I₂ f (criticalPoints i) = 0
  hessian_nondegenerate : ∀ x : M, (∀ i, x ≠ criticalPoints i) →
    Function.Surjective (mfderiv I₄ I₂ f x)
  generic_fiber_nonempty : ∃ (b : B₂),
    (∀ i, f (criticalPoints i) ≠ b) ∧
    Set.Nonempty (f ⁻¹' {b})
