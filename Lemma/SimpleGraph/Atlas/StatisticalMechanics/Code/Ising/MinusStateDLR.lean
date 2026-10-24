import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.MinusStateDLR
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[msdlr_finite_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MinusStateDLR.lean)
-/
@[path]
private lemma msdlr_finite_consistency_eq
  {d : Nat}
  {n m : Nat}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (hnm : n <= m)
  (beta h : Real) :
-- imply
  (∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) -> Real) omega ∂(minusMeasure d m beta h : Measure (ConfigSpace (Site d)))) = ∫ omega, f omega ∂(minusMeasure d m beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.msdlr_finite_consistency hnm beta h f

/--
[msdlr_specApply_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MinusStateDLR.lean)
-/
@[path]
private lemma msdlr_specApply_integral_eq_eq
  {d : Nat}
  {n : Nat}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (beta h : Real) :
-- imply
  ∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) -> Real) omega ∂(minusState d beta h : Measure (ConfigSpace (Site d))) = ∫ omega, f omega ∂(minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.msdlr_specApply_integral_eq beta h n f

/--
[msdlr_bind_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MinusStateDLR.lean)
-/
@[path]
private lemma msdlr_bind_eq_eq
  {d : Nat}
  {n : Nat}
-- given
  (beta h : Real) :
-- imply
  (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ (minusState d beta h : Measure (ConfigSpace (Site d))) = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.msdlr_bind_eq beta h n

/--
[compProd_rect_of_bind_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MinusStateDLR.lean)
-/
@[path]
private lemma compProd_rect_of_bind_eq_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {n : Nat}
  {s : Set (ConfigSpace (Site d))}
  {t : Set (ConfigSpace (Site d))}
-- given
  (beta h : Real)
  (hbind : (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu)
  (hs : MeasurableSet[outsideSigma (box d n)] s)
  (ht : MeasurableSet t) :
-- imply
  ((mu.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) beta h)) (s ×ˢ t) = mu (s ∩ t) := by
-- proof
  apply StatMech.Ising.compProd_rect_of_bind_eq beta h mu n hbind hs ht

/--
[compProd_trim_eq_of_bind_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MinusStateDLR.lean)
-/
@[path]
private lemma compProd_trim_eq_of_bind_eq_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {n : Nat}
-- given
  (beta h : Real)
  (hbind : (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu) :
-- imply
  (mu.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) beta h) = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _ ((outsideSigma (box d n)).prod inferInstance) (fun omega => (id omega, id omega)) mu := by
-- proof
  apply StatMech.Ising.compProd_trim_eq_of_bind_eq beta h mu n hbind

/--
[isDLRState_of_specFull_bind_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MinusStateDLR.lean)
-/
@[path]
private lemma isDLRState_of_specFull_bind_eq_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (beta h : Real)
  (hbind : ∀ n, (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu) :
-- imply
  IsDLRState d beta h mu := by
-- proof
  apply StatMech.Ising.isDLRState_of_specFull_bind_eq beta h mu hbind

/--
[msdlr_minusState_isDLR_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MinusStateDLR.lean)
-/
@[path]
private lemma msdlr_minusState_isDLR_uncond_eq
  {d : Nat}
-- given
  (beta h : Real) :
-- imply
  IsDLRState d beta h (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.msdlr_minusState_isDLR_uncond beta h


-- created on 2026-10-23
