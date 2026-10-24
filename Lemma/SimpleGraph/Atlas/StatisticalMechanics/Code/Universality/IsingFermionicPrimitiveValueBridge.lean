import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveValueBridge
open Filter Set Topology StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[PhysicalSplitRobinConsistencyInputs.primitive_tendsto_at_of_incidenceEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveValueBridge.lean)
-/
@[path]
private lemma primitive_tendsto_at_of_incidenceEmbedding_eq
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {Phi : Complex → Complex}
  {mesh bulkRate layerRate : Nat → Real}
  {H : PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {z : Complex}
-- given
  (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (e : ∀ k, FKIsingSquareInteriorRadialIncidence (N k) (hN k))
  (hembedding : Tendsto (fun k ↦ fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) (e k))) atTop (nhds z)) :
-- imply
  Tendsto (fun k ↦ (fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) (e k))) atTop (nhds (Phi z).im) ∧ Tendsto (fun k ↦ (fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) (e k))) atTop (nhds (Phi z).im) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs.primitive_tendsto_at_of_incidenceEmbedding H lipschitzConstant hPhi e z hembedding

/--
[isingFermionicEntireSquarePrimitive_tendsto_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveValueBridge.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_tendsto_at_eq
  {F : Nat → Complex → Complex}
  {f : Complex → Complex}
  {z : Complex}
-- given
  (hF : ∀ n, Differentiable Complex (F n))
  (hf : Differentiable Complex f)
  (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ) :
-- imply
  Tendsto (fun n ↦ isingFermionicEntireSquarePrimitive (F n) z) atTop (nhds (isingFermionicEntireSquarePrimitive f z)) := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_tendsto_at hF hf hlimit z

/--
[isingFermionic_dense_primitive_identification_of_finite_scale_values](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveValueBridge.lean)
-/
@[path]
private lemma isingFermionic_dense_primitive_identification_of_finite_scale_values_eq
  {F : Nat → Complex → Complex}
  {f Phi target : Complex → Complex}
  {S : Set Complex}
  {C : Real}
  {root : Complex}
-- given
  (hF : ∀ n, Differentiable Complex (F n))
  (hf : Differentiable Complex f)
  (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
  (hvalues : ∀ z ∈ S, Tendsto (fun n ↦ (isingFermionicEntireSquarePrimitive (F n) z).im) atTop (nhds ((Phi z).im + C)))
  (hroot : Tendsto (fun n ↦ F n root) atTop (nhds (target root))) :
-- imply
  Set.EqOn (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im) (fun z ↦ (Phi z).im + C) S ∧ f root = target root := by
-- proof
  apply StatMech.Universality.isingFermionic_dense_primitive_identification_of_finite_scale_values hF hf hlimit S C hvalues root hroot

/--
[isingFermionicEntireSquarePrimitive_im_tendsto_of_discretePrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveValueBridge.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_im_tendsto_of_discretePrimitive_eq
  {F : Nat → Complex → Complex}
  {Phi : Complex → Complex}
  {discretePrimitive : Nat → Complex → Real}
  {C : Real}
  {z : Complex}
-- given
  (hcompare : Tendsto (fun n ↦ (isingFermionicEntireSquarePrimitive (F n) z).im - discretePrimitive n z) atTop (nhds 0))
  (hdiscrete : Tendsto (fun n ↦ discretePrimitive n z) atTop (nhds ((Phi z).im + C))) :
-- imply
  Tendsto (fun n ↦ (isingFermionicEntireSquarePrimitive (F n) z).im) atTop (nhds ((Phi z).im + C)) := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_im_tendsto_of_discretePrimitive discretePrimitive C z hcompare hdiscrete

/--
[fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveValueBridge.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveValues_eq
  {I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
  {S : Set Complex}
  {C : Real}
-- given
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hSdense : Dense S)
  (hvalues : ∀ z ∈ S, Tendsto (fun k ↦ (isingFermionicEntireSquarePrimitive (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k) z).im) atTop (nhds ((Phi z).im + C)))
  (hroot : Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧ TendstoLocallyUniformlyOn (deriv ∘ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant) (deriv target) atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveValues I target Phi htarget htarget_ne hPhi hPhideriv E S hSdense C hvalues hroot

/--
[fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_discretePrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveValueBridge.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_discretePrimitive_eq
  {I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
  {S : Set Complex}
  {C : Real}
  {discretePrimitive : Nat → Complex → Real}
-- given
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hSdense : Dense S)
  (hcompare : ∀ z ∈ S, Tendsto (fun k ↦ (isingFermionicEntireSquarePrimitive (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k) z).im - discretePrimitive k z) atTop (nhds 0))
  (hdiscrete : ∀ z ∈ S, Tendsto (fun k ↦ discretePrimitive k z) atTop (nhds ((Phi z).im + C)))
  (hroot : Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧ TendstoLocallyUniformlyOn (deriv ∘ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant) (deriv target) atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_discretePrimitive I target Phi htarget htarget_ne hPhi hPhideriv E S hSdense C discretePrimitive hcompare hdiscrete hroot


-- created on 2026-10-23
