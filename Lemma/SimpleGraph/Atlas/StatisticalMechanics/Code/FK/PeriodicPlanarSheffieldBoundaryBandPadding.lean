import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_common_leftBoundaryExhaustion_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma exists_common_leftBoundaryExhaustion_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {source : ι → Finset V}
  {epsilon : Real}
-- given
  (hinside : ∀ i, (source i : Set V) ⊆ E.rightHalfPlaneVertices r)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ i, (source i : Set V) ⊆ E.leftBoundaryExhaustionVertices r radius ∧ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (source i : Set V) (E.rightHalfPlaneBoundaryVertices r)) - epsilon < mu.real (E.leftBoundaryExhaustionEvent r (source i : Set V) radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_common_leftBoundaryExhaustion_measureReal_gt E mu r source hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {shift : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rightHalfPlaneVertices r)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.leftBoundaryExhaustionVertices r radius ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.leftBoundaryExhaustionEvent r (P.shift (shift i) '' (S : Set V)) radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {shift : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆ {v | E.vertexCoord v 0 ≤ -r})
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rectVertices (-(r + radius)) (-r) (-(radius : Real)) radius ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent (-(r + radius)) (-r) (-(radius : Real)) radius (P.shift (shift i) '' (S : Set V)) (E.rectRightBoundaryVertices (-(r + radius)) (-r) (-(radius : Real)) radius)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {shift : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆ {v | r ≤ E.vertexCoord v 1})
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rectVertices (-(radius : Real)) radius r (r + radius) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent (-(radius : Real)) radius r (r + radius) (P.shift (shift i) '' (S : Set V)) (E.rectBottomBoundaryVertices (-(radius : Real)) radius r (r + radius))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma exists_translatedFamily_topBoundaryExhaustion_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {shift : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆ {v | E.vertexCoord v 1 ≤ -r})
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rectVertices (-(radius : Real)) radius (-(r + radius)) (-r) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent (-(radius : Real)) radius (-(r + radius)) (-r) (P.shift (shift i) '' (S : Set V)) (E.rectTopBoundaryVertices (-(radius : Real)) radius (-(r + radius)) (-r))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.leftBoundaryExhaustion_to_commonSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma leftBoundaryExhaustion_to_commonSquare_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {radius M : Nat}
  {S : Set V}
  {p : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hM : radius ≤ M)
  (hS : S ⊆ E.rectVertices 0 radius (-(radius : Real)) radius)
  (hp : p < mu.real (E.rectSideConnectionEvent 0 radius (-(radius : Real)) radius S (E.rectLeftBoundaryVertices 0 radius (-(radius : Real)) radius))) :
-- imply
  P.shift (horizontalShift (-(M : Int))) '' S ⊆ E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧ p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M (P.shift (horizontalShift (-(M : Int))) '' S) (E.rectLeftBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.leftBoundaryExhaustion_to_commonSquare E mu hTI radius M hM S p hS hp

/--
[PeriodicPlaneEmbedding.rightBoundaryExhaustion_to_commonSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma rightBoundaryExhaustion_to_commonSquare_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {radius M : Nat}
  {S : Set V}
  {p : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hM : radius ≤ M)
  (hS : S ⊆ E.rectVertices (-(radius : Real)) 0 (-(radius : Real)) radius)
  (hp : p < mu.real (E.rectSideConnectionEvent (-(radius : Real)) 0 (-(radius : Real)) radius S (E.rectRightBoundaryVertices (-(radius : Real)) 0 (-(radius : Real)) radius))) :
-- imply
  P.shift (horizontalShift (M : Int)) '' S ⊆ E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧ p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M (P.shift (horizontalShift (M : Int)) '' S) (E.rectRightBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightBoundaryExhaustion_to_commonSquare E mu hTI radius M hM S p hS hp

/--
[PeriodicPlaneEmbedding.bottomBoundaryExhaustion_to_commonSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma bottomBoundaryExhaustion_to_commonSquare_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {radius M : Nat}
  {S : Set V}
  {p : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hM : radius ≤ M)
  (hS : S ⊆ E.rectVertices (-(radius : Real)) radius 0 radius)
  (hp : p < mu.real (E.rectSideConnectionEvent (-(radius : Real)) radius 0 radius S (E.rectBottomBoundaryVertices (-(radius : Real)) radius 0 radius))) :
-- imply
  P.shift (verticalShift (-(M : Int))) '' S ⊆ E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧ p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M (P.shift (verticalShift (-(M : Int))) '' S) (E.rectBottomBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.bottomBoundaryExhaustion_to_commonSquare E mu hTI radius M hM S p hS hp

/--
[PeriodicPlaneEmbedding.topBoundaryExhaustion_to_commonSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma topBoundaryExhaustion_to_commonSquare_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {radius M : Nat}
  {S : Set V}
  {p : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hM : radius ≤ M)
  (hS : S ⊆ E.rectVertices (-(radius : Real)) radius (-(radius : Real)) 0)
  (hp : p < mu.real (E.rectSideConnectionEvent (-(radius : Real)) radius (-(radius : Real)) 0 S (E.rectTopBoundaryVertices (-(radius : Real)) radius (-(radius : Real)) 0))) :
-- imply
  P.shift (verticalShift (M : Int)) '' S ⊆ E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧ p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M (P.shift (verticalShift (M : Int)) '' S) (E.rectTopBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.topBoundaryExhaustion_to_commonSquare E mu hTI radius M hM S p hS hp

/--
[le_commonPrimalDualBandHalfWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma le_commonPrimalDualBandHalfWidth_eq
  [DecidableEq V]
  [Countable V]
  {primalLeft primalRight primalBottom primalTop dualLeft dualRight dualBottom dualTop : Nat} :
-- imply
  let M := commonPrimalDualBandHalfWidth primalLeft primalRight primalBottom primalTop dualLeft dualRight dualBottom dualTop primalLeft ≤ M ∧ primalRight ≤ M ∧ primalBottom ≤ M ∧ primalTop ≤ M ∧ dualLeft ≤ M ∧ dualRight ≤ M ∧ dualBottom ≤ M ∧ dualTop ≤ M := by
-- proof
  apply StatMech.FK.PeriodicPlanar.le_commonPrimalDualBandHalfWidth primalLeft primalRight primalBottom primalTop dualLeft dualRight dualBottom dualTop

/--
[boundaryBandPreferenceColor_eq_true_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma boundaryBandPreferenceColor_eq_true_of_lower_eq
  [DecidableEq V]
  [Countable V]
  {margin extent position : Nat}
  {epsilon preferred opposite : Real}
-- given
  (hposition : position ≤ margin) :
-- imply
  boundaryBandPreferenceColor margin extent position epsilon preferred opposite = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryBandPreferenceColor_eq_true_of_lower hposition

/--
[boundaryBandPreferenceColor_eq_false_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma boundaryBandPreferenceColor_eq_false_of_upper_eq
  [DecidableEq V]
  [Countable V]
  {margin extent position : Nat}
  {epsilon preferred opposite : Real}
-- given
  (hsep : 2 * margin < extent)
  (hposition : extent ≤ position + margin) :
-- imply
  boundaryBandPreferenceColor margin extent position epsilon preferred opposite = false := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryBandPreferenceColor_eq_false_of_upper hsep hposition

/--
[boundaryBandPreferenceColor_true_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma boundaryBandPreferenceColor_true_imp_eq
  [DecidableEq V]
  [Countable V]
  {margin extent position : Nat}
  {epsilon preferred opposite p : Real}
-- given
  (hepsilon : 0 ≤ epsilon)
  (hsep : 2 * margin < extent)
  (hopposite : opposite ≤ 1)
  (hlower : position ≤ margin → p ≤ preferred)
  (hdefect : 1 - p ≤ epsilon)
  (hcolor : boundaryBandPreferenceColor margin extent position epsilon preferred opposite = true) :
-- imply
  opposite ≤ preferred + epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryBandPreferenceColor_true_imp hepsilon hsep hopposite hlower hdefect hcolor

/--
[boundaryBandPreferenceColor_false_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean)
-/
@[path]
private lemma boundaryBandPreferenceColor_false_imp_eq
  [DecidableEq V]
  [Countable V]
  {margin extent position : Nat}
  {epsilon preferred opposite p : Real}
-- given
  (hepsilon : 0 ≤ epsilon)
  (hsep : 2 * margin < extent)
  (hpreferred : preferred ≤ 1)
  (hupper : extent ≤ position + margin → p ≤ opposite)
  (hdefect : 1 - p ≤ epsilon)
  (hcolor : boundaryBandPreferenceColor margin extent position epsilon preferred opposite = false) :
-- imply
  preferred ≤ opposite + epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryBandPreferenceColor_false_imp hepsilon hsep hpreferred hupper hdefect hcolor


-- created on 2026-10-23
