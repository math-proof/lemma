import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part5
open Filter Metric Set Topology StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[isingProj_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma isingProj_sub_eq
  {e x y : Complex} :
-- imply
  isingProj e x - isingProj e y = isingProj e (x - y) := by
-- proof
  apply StatMech.Universality.isingProj_sub e x y

/--
[isingProj_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma isingProj_norm_le_eq
  {e z : Complex}
-- given
  (he : Complex.normSq e = 1) :
-- imply
  ‖isingProj e z‖ ≤ ‖z‖ := by
-- proof
  apply StatMech.Universality.isingProj_norm_le e z he

/--
[isingProj_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma isingProj_dist_le_eq
  {e x y : Complex}
-- given
  (he : Complex.normSq e = 1) :
-- imply
  dist (isingProj e x) (isingProj e y) ≤ dist x y := by
-- proof
  apply StatMech.Universality.isingProj_dist_le e x y he

/--
[isingProj_dist_le_of_nearby_holder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma isingProj_dist_le_of_nearby_holder_eq
  {e : Complex}
  {F : Complex → Complex}
  {sample embedded observable : Complex}
  {C alpha : NNReal}
-- given
  (he : Complex.normSq e = 1)
  (hholder : HolderWith C alpha F)
  (hsample : isingProj e (F sample) = observable) :
-- imply
  dist (isingProj e (F embedded)) observable ≤ C * dist embedded sample ^ (alpha : Real) := by
-- proof
  apply StatMech.Universality.isingProj_dist_le_of_nearby_holder e F sample embedded observable C alpha he hholder hsample

/--
[norm_sub_le_two_mul_of_proj_one_I](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma norm_sub_le_two_mul_of_proj_one_I_eq
  {x y z : Complex}
-- given
  (hxy : isingProj 1 x = isingProj 1 y)
  (hyz : isingProj Complex.I y = isingProj Complex.I z) :
-- imply
  ‖x - y‖ ≤ 2 * ‖x - z‖ := by
-- proof
  apply StatMech.Universality.norm_sub_le_two_mul_of_proj_one_I x y z hxy hyz

/--
[norm_sub_le_two_mul_of_proj_I_negOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma norm_sub_le_two_mul_of_proj_I_negOne_eq
  {x y z : Complex}
-- given
  (hxy : isingProj Complex.I x = isingProj Complex.I y)
  (hyz : isingProj (-1) y = isingProj (-1) z) :
-- imply
  ‖x - y‖ ≤ 2 * ‖x - z‖ := by
-- proof
  apply StatMech.Universality.norm_sub_le_two_mul_of_proj_I_negOne x y z hxy hyz

/--
[norm_sub_le_two_mul_of_proj_negOne_negI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma norm_sub_le_two_mul_of_proj_negOne_negI_eq
  {x y z : Complex}
-- given
  (hxy : isingProj (-1) x = isingProj (-1) y)
  (hyz : isingProj (-Complex.I) y = isingProj (-Complex.I) z) :
-- imply
  ‖x - y‖ ≤ 2 * ‖x - z‖ := by
-- proof
  apply StatMech.Universality.norm_sub_le_two_mul_of_proj_negOne_negI x y z hxy hyz

/--
[norm_sub_le_two_mul_of_proj_negI_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma norm_sub_le_two_mul_of_proj_negI_one_eq
  {x y z : Complex}
-- given
  (hxy : isingProj (-Complex.I) x = isingProj (-Complex.I) y)
  (hyz : isingProj 1 y = isingProj 1 z) :
-- imply
  ‖x - y‖ ≤ 2 * ‖x - z‖ := by
-- proof
  apply StatMech.Universality.norm_sub_le_two_mul_of_proj_negI_one x y z hxy hyz

/--
[IsingSquareSHolomorphicQuad.projection_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma projection_cycle_eq
  {north east south west : Complex}
-- given
  (h : IsingSquareSHolomorphicQuad south west north east) :
-- imply
  isingProj 1 north = isingProj 1 east ∧ isingProj Complex.I east = isingProj Complex.I south ∧ isingProj (-1) south = isingProj (-1) west ∧ isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
-- proof
  apply StatMech.Universality.IsingSquareSHolomorphicQuad.projection_cycle north east south west h

/--
[projectionCycle_crossParity_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma projectionCycle_crossParity_norm_sub_le_eq
  {north east south west : Complex}
  {delta : Real}
-- given
  (hNE : isingProj 1 north = isingProj 1 east)
  (hES : isingProj Complex.I east = isingProj Complex.I south)
  (hSW : isingProj (-1) south = isingProj (-1) west)
  (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
  (hNS : ‖north - south‖ ≤ delta)
  (hEW : ‖east - west‖ ≤ delta) :
-- imply
  ‖north - east‖ ≤ 2 * delta ∧ ‖east - south‖ ≤ 2 * delta ∧ ‖south - west‖ ≤ 2 * delta ∧ ‖west - north‖ ≤ 2 * delta := by
-- proof
  apply StatMech.Universality.projectionCycle_crossParity_norm_sub_le north east south west delta hNE hES hSW hWN hNS hEW

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_even_projectionCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_even_projectionCycle_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ isingProj 1 north = isingProj 1 east ∧ isingProj Complex.I east = isingProj Complex.I south ∧ isingProj (-1) south = isingProj (-1) west ∧ isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_even_projectionCycle n m i j hn hm hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_odd_projectionCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_odd_projectionCycle_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ isingProj 1 south = isingProj 1 west ∧ isingProj Complex.I west = isingProj Complex.I north ∧ isingProj (-1) north = isingProj (-1) east ∧ isingProj (-Complex.I) east = isingProj (-Complex.I) south := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_odd_projectionCycle n m i j hn hm hi0 hi1 hj0 hj1 hodd

/--
[MeshUniformFullHolder.equicontinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma equicontinuous_eq
  {A : FKIsingCaratheodoryApproximation}
  {F : Nat → Complex → Complex}
  {H : MeshUniformFullHolder F} :
-- imply
  Equicontinuous F := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.MeshUniformFullHolder.equicontinuous A H

/--
[BoundaryRadialTensorTentGeometry.interpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma interpolant_continuous_eq
  {A : FKIsingCaratheodoryApproximation}
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {k : Nat} :
-- imply
  Continuous (BoundaryRadialTensorTentGeometry.interpolant A G k) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.interpolant_continuous A A G k

/--
[BoundaryRadialTensorTentGeometry.projectedMedial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma projectedMedial_eq
  {A : FKIsingCaratheodoryApproximation}
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {k : Nat}
  {e : A.M k} :
-- imply
  isingProj (BoundaryRadialTensorTentGeometry.tangent A G k e) (BoundaryRadialTensorTentGeometry.interpolant A G k (A.medialEmbedding k e)) = @FKIsingDobrushinDomain.normalizedFermionicObservable (A.P k) (A.M k) (A.decEqM k) (A.dobrushin k) (A.mesh k) e := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.projectedMedial A A G k e

/--
[StableFullMedialInterpolation.hasCompactLocalBounds_of_holder_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma hasCompactLocalBounds_of_holder_anchor_eq
  {A : FKIsingCaratheodoryApproximation}
  {tangent : ∀ n, A.M n → Complex}
  {I : A.StableFullMedialInterpolation tangent}
  {H : MeshUniformFullHolder I.interpolant}
  {B : Real}
-- given
  (hanchor : ∀ n, ‖I.interpolant n A.root‖ ≤ B) :
-- imply
  I.HasCompactLocalBounds := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.hasCompactLocalBounds_of_holder_anchor A I H B hanchor

/--
[StableFullMedialInterpolation.locallyUniformlySequentiallyPrecompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma locallyUniformlySequentiallyPrecompact_eq
  {A : FKIsingCaratheodoryApproximation}
  {tangent : ∀ n, A.M n → Complex}
  {I : A.StableFullMedialInterpolation tangent}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (hbounded : I.HasCompactLocalBounds) :
-- imply
  StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact I.interpolant A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.locallyUniformlySequentiallyPrecompact A I E hbounded

/--
[StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma scalingLimit_of_compactBounds_and_moreraPrimitive_eq
  {A : FKIsingCaratheodoryApproximation}
  {tangent : ∀ n, A.M n → Complex}
  {I : A.StableFullMedialInterpolation tangent}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (htarget : DifferentiableOn Complex target A.U)
  (htarget_ne : target A.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi A.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
  (hbounded : I.HasCompactLocalBounds)
  (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive A I target Phi) :
-- imply
  TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive A I target Phi htarget htarget_ne hPhi hPhideriv E hbounded hidentify

/--
[StableFullMedialInterpolation.scalingLimit_of_tensorTentGridHolder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma scalingLimit_of_tensorTentGridHolder_eq
  {A : FKIsingCaratheodoryApproximation}
  {tangent : ∀ n, A.M n → Complex}
  {I : A.StableFullMedialInterpolation tangent}
  {H : MeshUniformFullHolder I.interpolant}
  {B : Real}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (hanchorBound : ∀ n, ‖I.interpolant n A.root‖ ≤ B)
  (htarget : DifferentiableOn Complex target A.U)
  (htarget_ne : target A.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi A.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
  (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive A I target Phi) :
-- imply
  TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.scalingLimit_of_tensorTentGridHolder A I H B hanchorBound target Phi htarget htarget_ne hPhi hPhideriv E hidentify

/--
[StableFullMedialInterpolation.projectedLiteralObservable_tendsto_on_compacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean)
-/
@[path]
private lemma projectedLiteralObservable_tendsto_on_compacts_eq
  {A : FKIsingCaratheodoryApproximation}
  {tangent : ∀ n, A.M n → Complex}
  {I : A.StableFullMedialInterpolation tangent}
  {target : Complex → Complex}
  {K : Set Complex}
  {epsilon : Real}
-- given
  (hunit : ∀ n e, Complex.normSq (tangent n e) = 1)
  (hlimit : TendstoLocallyUniformlyOn I.interpolant target atTop A.U)
  (hK : IsCompact K)
  (hKU : K ⊆ A.U)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ n in atTop, ∀ e : A.M n, A.medialEmbedding n e ∈ K → dist (@FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e) (isingProj (tangent n e) (target (A.medialEmbedding n e))) < epsilon := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.projectedLiteralObservable_tendsto_on_compacts A I hunit target hlimit K hK hKU epsilon hepsilon


-- created on 2026-10-23
