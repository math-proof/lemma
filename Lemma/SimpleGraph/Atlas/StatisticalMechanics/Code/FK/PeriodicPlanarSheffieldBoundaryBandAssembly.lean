import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part8
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_translatedFamily_leftBoundaryExhaustion_centered_eq
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
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rectVertices r (r + radius) ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent r (r + radius) ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) (P.shift (shift i) '' (S : Set V)) (E.rectLeftBoundaryVertices r (r + radius) ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_centered E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_uniform_tangentialPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_leftBoundaryExhaustion_uniform_tangentialPlacement_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {normal : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆ E.rightHalfPlaneVertices r)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i, let shift := normal i + verticalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices r (r + radius) ((tangent i : Real) - radius) ((tangent i : Real) + radius) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent r (r + radius) ((tangent i : Real) - radius) ((tangent i : Real) + radius) (P.shift shift '' (S : Set V)) (E.rectLeftBoundaryVertices r (r + radius) ((tangent i : Real) - radius) ((tangent i : Real) + radius))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_uniform_tangentialPlacement E mu hFKG hTI hunique r S normal hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_translatedFamily_rightBoundaryExhaustion_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_translatedFamily_rightBoundaryExhaustion_centered_eq
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
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rectVertices (-(r + radius)) (-r) ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent (-(r + radius)) (-r) ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) (P.shift (shift i) '' (S : Set V)) (E.rectRightBoundaryVertices (-(r + radius)) (-r) ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_rightBoundaryExhaustion_centered E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_translatedFamily_bottomBoundaryExhaustion_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_translatedFamily_bottomBoundaryExhaustion_centered_eq
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
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rectVertices ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius) r (r + radius) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius) r (r + radius) (P.shift (shift i) '' (S : Set V)) (E.rectBottomBoundaryVertices ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius) r (r + radius))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_bottomBoundaryExhaustion_centered E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_translatedFamily_topBoundaryExhaustion_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_translatedFamily_topBoundaryExhaustion_centered_eq
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
  ∃ radius : Nat, ∀ i, P.shift (shift i) '' (S : Set V) ⊆ E.rectVertices ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius) (-(r + radius)) (-r) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius) (-(r + radius)) (-r) (P.shift (shift i) '' (S : Set V)) (E.rectTopBoundaryVertices ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius) (-(r + radius)) (-r))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedFamily_topBoundaryExhaustion_centered E mu hFKG hTI hunique r S shift hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_rightBoundaryExhaustion_uniform_tangentialPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_rightBoundaryExhaustion_uniform_tangentialPlacement_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {normal : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆ {v | E.vertexCoord v 0 ≤ -r})
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i, let shift := normal i + verticalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices (-(r + radius)) (-r) ((tangent i : Real) - radius) ((tangent i : Real) + radius) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent (-(r + radius)) (-r) ((tangent i : Real) - radius) ((tangent i : Real) + radius) (P.shift shift '' (S : Set V)) (E.rectRightBoundaryVertices (-(r + radius)) (-r) ((tangent i : Real) - radius) ((tangent i : Real) + radius))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_rightBoundaryExhaustion_uniform_tangentialPlacement E mu hFKG hTI hunique r S normal hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_bottomBoundaryExhaustion_uniform_tangentialPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_bottomBoundaryExhaustion_uniform_tangentialPlacement_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {normal : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆ {v | r ≤ E.vertexCoord v 1})
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i, let shift := normal i + horizontalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices ((tangent i : Real) - radius) ((tangent i : Real) + radius) r (r + radius) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent ((tangent i : Real) - radius) ((tangent i : Real) + radius) r (r + radius) (P.shift shift '' (S : Set V)) (E.rectBottomBoundaryVertices ((tangent i : Real) - radius) ((tangent i : Real) + radius) r (r + radius))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_bottomBoundaryExhaustion_uniform_tangentialPlacement E mu hFKG hTI hunique r S normal hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_topBoundaryExhaustion_uniform_tangentialPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_topBoundaryExhaustion_uniform_tangentialPlacement_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
  {r : Real}
  {S : Finset V}
  {normal : ι → Site 2}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆ {v | E.vertexCoord v 1 ≤ -r})
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i, let shift := normal i + horizontalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices ((tangent i : Real) - radius) ((tangent i : Real) + radius) (-(r + radius)) (-r) ∧ (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon < mu.real (E.rectSideConnectionEvent ((tangent i : Real) - radius) ((tangent i : Real) + radius) (-(r + radius)) (-r) (P.shift shift '' (S : Set V)) (E.rectTopBoundaryVertices ((tangent i : Real) - radius) ((tangent i : Real) + radius) (-(r + radius)) (-r))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_topBoundaryExhaustion_uniform_tangentialPlacement E mu hFKG hTI hunique r S normal hinside hepsilon

/--
[PeriodicPlaneEmbedding.exists_orbitBox_boundaryBandSeed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_orbitBox_boundaryBandSeed_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {delta : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (N width height : Nat)
  (hdelta : 0 < delta) :
-- imply
  Nonempty (E.BoundaryBandSeed mu (P.orbitBox N) width height ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_orbitBox_boundaryBandSeed E mu hFKG hTI hunique N width height hdelta

/--
[PeriodicGraph.componentGridImage_eq_normalShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma componentGridImage_eq_normalShift_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {base normal : Site 2}
  {width height : Nat}
  {v : PreferenceGridVertex width height} :
-- imply
  ((S.image (P.shift (base + normal))).image (P.shift (preferenceGridSite v)) : Set V) = P.shift normal '' (P.shift (base + preferenceGridSite v) '' (S : Set V)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.componentGridImage_eq_normalShift P S base normal v

/--
[PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.template_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma template_subset_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Finset V}
  {width height M : Nat}
  {p : Real}
  {data : E.CommonSquareBoundaryBandData mu S width height M p}
  {v : PreferenceGridVertex width height} :
-- imply
  ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) ⊆ E.rectVertices (-(M : Real)) M (-(M : Real)) M := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.template_subset E mu data v

/--
[PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.leftScore_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma leftScore_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {width height M : Nat}
  {p : Real}
  {data : E.CommonSquareBoundaryBandData mu S width height M p}
  {v : PreferenceGridVertex width height} :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.leftScore_gt E mu data v

/--
[PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.rightScore_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma rightScore_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {width height M : Nat}
  {p : Real}
  {data : E.CommonSquareBoundaryBandData mu S width height M p}
  {v : PreferenceGridVertex width height} :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.rightScore_gt E mu data v

/--
[PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.bottomScore_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma bottomScore_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {width height M : Nat}
  {p : Real}
  {data : E.CommonSquareBoundaryBandData mu S width height M p}
  {v : PreferenceGridVertex width height} :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.bottomScore_gt E mu data v

/--
[PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.topScore_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma topScore_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {width height M : Nat}
  {p : Real}
  {data : E.CommonSquareBoundaryBandData mu S width height M p}
  {v : PreferenceGridVertex width height} :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.topScore_gt E mu data v

/--
[exists_matched_commonSquareBoundaryBandData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_matched_commonSquareBoundaryBandData_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {width height : Nat}
  {p pDual : Real}
  {primal : E.BoundaryBandSeed mu S width height p}
  {dual : Edual.BoundaryBandSeed muDual Sdual width height pDual}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  ∃ M : Nat, Nonempty (E.CommonSquareBoundaryBandData mu S width height M p) ∧ Nonempty (Edual.CommonSquareBoundaryBandData muDual Sdual width height M pDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_matched_commonSquareBoundaryBandData E Edual mu muDual hTI hTIDual primal dual

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_tangential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma left_tangential_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {tangent : Fin (margin + 1) → Int}
  {i : Fin (margin + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  let shift := seed.baseLeft + horizontalShift i.val + verticalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices 0 seed.radiusLeft ((tangent i : Real) - seed.radiusLeft) ((tangent i : Real) + seed.radiusLeft) ∧ p < mu.real (E.rectSideConnectionEvent 0 seed.radiusLeft ((tangent i : Real) - seed.radiusLeft) ((tangent i : Real) + seed.radiusLeft) (P.shift shift '' (S : Set V)) (E.rectLeftBoundaryVertices 0 seed.radiusLeft ((tangent i : Real) - seed.radiusLeft) ((tangent i : Real) + seed.radiusLeft))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_tangential E mu hTI seed tangent i

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_tangential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma right_tangential_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {tangent : Fin (margin + 1) → Int}
  {i : Fin (margin + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  let shift := seed.baseRight + horizontalShift (-(i.val : Int)) + verticalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices (-(seed.radiusRight : Real)) 0 ((tangent i : Real) - seed.radiusRight) ((tangent i : Real) + seed.radiusRight) ∧ p < mu.real (E.rectSideConnectionEvent (-(seed.radiusRight : Real)) 0 ((tangent i : Real) - seed.radiusRight) ((tangent i : Real) + seed.radiusRight) (P.shift shift '' (S : Set V)) (E.rectRightBoundaryVertices (-(seed.radiusRight : Real)) 0 ((tangent i : Real) - seed.radiusRight) ((tangent i : Real) + seed.radiusRight))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_tangential E mu hTI seed tangent i

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_tangential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma bottom_tangential_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {tangent : Fin (margin + 1) → Int}
  {i : Fin (margin + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  let shift := seed.baseBottom + verticalShift i.val + horizontalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices ((tangent i : Real) - seed.radiusBottom) ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom ∧ p < mu.real (E.rectSideConnectionEvent ((tangent i : Real) - seed.radiusBottom) ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom (P.shift shift '' (S : Set V)) (E.rectBottomBoundaryVertices ((tangent i : Real) - seed.radiusBottom) ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_tangential E mu hTI seed tangent i

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_tangential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma top_tangential_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {tangent : Fin (margin + 1) → Int}
  {i : Fin (margin + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  let shift := seed.baseTop + verticalShift (-(i.val : Int)) + horizontalShift (tangent i) P.shift shift '' (S : Set V) ⊆ E.rectVertices ((tangent i : Real) - seed.radiusTop) ((tangent i : Real) + seed.radiusTop) (-(seed.radiusTop : Real)) 0 ∧ p < mu.real (E.rectSideConnectionEvent ((tangent i : Real) - seed.radiusTop) ((tangent i : Real) + seed.radiusTop) (-(seed.radiusTop : Real)) 0 (P.shift shift '' (S : Set V)) (E.rectTopBoundaryVertices ((tangent i : Real) - seed.radiusTop) ((tangent i : Real) + seed.radiusTop) (-(seed.radiusTop : Real)) 0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_tangential E mu hTI seed tangent i

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_translate_to_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma left_translate_to_rect_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {i : Fin (margin + 1)}
  {z : Site 2}
  {b c d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hb : (seed.radiusLeft : Real) + z 0 ≤ b)
  (hc : c ≤ -(seed.radiusLeft : Real) + z 1)
  (hd : (seed.radiusLeft : Real) + z 1 ≤ d) :
-- imply
  P.shift z '' (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)) ⊆ E.rectVertices (z 0) b c d ∧ p < mu.real (E.rectSideConnectionEvent (z 0) b c d (P.shift z '' (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V))) (E.rectLeftBoundaryVertices (z 0) b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_translate_to_rect E mu hTI seed i z b c d hb hc hd

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_translate_to_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma right_translate_to_rect_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {i : Fin (margin + 1)}
  {z : Site 2}
  {a c d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (ha : a ≤ -(seed.radiusRight : Real) + z 0)
  (hc : c ≤ -(seed.radiusRight : Real) + z 1)
  (hd : (seed.radiusRight : Real) + z 1 ≤ d) :
-- imply
  P.shift z '' (P.shift (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V)) ⊆ E.rectVertices a (z 0) c d ∧ p < mu.real (E.rectSideConnectionEvent a (z 0) c d (P.shift z '' (P.shift (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V))) (E.rectRightBoundaryVertices a (z 0) c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_translate_to_rect E mu hTI seed i z a c d ha hc hd

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_translate_to_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma bottom_translate_to_rect_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {i : Fin (margin + 1)}
  {z : Site 2}
  {a b d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (ha : a ≤ -(seed.radiusBottom : Real) + z 0)
  (hb : (seed.radiusBottom : Real) + z 0 ≤ b)
  (hd : (seed.radiusBottom : Real) + z 1 ≤ d) :
-- imply
  P.shift z '' (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)) ⊆ E.rectVertices a b (z 1) d ∧ p < mu.real (E.rectSideConnectionEvent a b (z 1) d (P.shift z '' (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V))) (E.rectBottomBoundaryVertices a b (z 1) d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_translate_to_rect E mu hTI seed i z a b d ha hb hd

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_translate_to_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma top_translate_to_rect_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin : Nat}
  {p : Real}
  {seed : E.NormalBoundaryBandSeed mu S margin p}
  {i : Fin (margin + 1)}
  {z : Site 2}
  {a b c : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (ha : a ≤ -(seed.radiusTop : Real) + z 0)
  (hb : (seed.radiusTop : Real) + z 0 ≤ b)
  (hc : c ≤ -(seed.radiusTop : Real) + z 1) :
-- imply
  P.shift z '' (P.shift (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V)) ⊆ E.rectVertices a b c (z 1) ∧ p < mu.real (E.rectSideConnectionEvent a b c (z 1) (P.shift z '' (P.shift (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V))) (E.rectTopBoundaryVertices a b c (z 1))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_translate_to_rect E mu hTI seed i z a b c ha hb hc

/--
[PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandSeed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_orbitBox_normalBoundaryBandSeed_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {N margin : Nat}
  {delta : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdelta : 0 < delta) :
-- imply
  Nonempty (E.NormalBoundaryBandSeed mu (P.orbitBox N) margin ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandSeed E mu hFKG hTI hunique N margin hdelta

/--
[PeriodicGraph.normalShift_image_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma normalShift_image_add_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {P : PeriodicGraph V}
  {S : Set V}
  {base band normal : Site 2} :
-- imply
  P.shift normal '' (P.shift (base + band) '' S) = P.shift (base + normal + band) '' S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.normalShift_image_add P S base band normal

/--
[exists_alternating_dominating_sequences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_alternating_dominating_sequences_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {f g : Nat → Nat} :
-- imply
  ∃ x y : Nat → Nat, Tendsto x atTop atTop ∧ Tendsto y atTop atTop ∧ (∀ n, f (x n) ≤ y n) ∧ (∀ n, g (y n) ≤ x (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alternating_dominating_sequences f g

/--
[normalBand_left_source_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma normalBand_left_source_aligned_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {baseLeft gridBase : Site 2}
  {i j : Nat} :
-- imply
  baseLeft + horizontalShift i + (gridBase - baseLeft + verticalShift j) = gridBase + horizontalShift i + verticalShift j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.normalBand_left_source_aligned baseLeft gridBase i j

/--
[normalBand_right_source_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma normalBand_right_source_aligned_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {baseRight gridBase : Site 2}
  {width i j : Nat} :
-- imply
  baseRight + horizontalShift (-(i : Int)) + (gridBase - baseRight + horizontalShift width + verticalShift j) = gridBase + horizontalShift ((width : Int) - i) + verticalShift j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.normalBand_right_source_aligned baseRight gridBase width i j

/--
[normalBand_bottom_source_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma normalBand_bottom_source_aligned_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {baseBottom gridBase : Site 2}
  {i j : Nat} :
-- imply
  baseBottom + verticalShift j + (gridBase - baseBottom + horizontalShift i) = gridBase + horizontalShift i + verticalShift j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.normalBand_bottom_source_aligned baseBottom gridBase i j

/--
[normalBand_top_source_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma normalBand_top_source_aligned_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {baseTop gridBase : Site 2}
-- given
  (height i j : Nat) :
-- imply
  baseTop + verticalShift (-(j : Int)) + (gridBase - baseTop + verticalShift height + horizontalShift i) = gridBase + horizontalShift i + verticalShift ((height : Int) - j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.normalBand_top_source_aligned baseTop gridBase height i j

/--
[PeriodicPlaneEmbedding.setHitsInfinite_subset_mixedRectSideConnection_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma setHitsInfinite_subset_mixedRectSideConnection_union_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a0 b0 c0 d0 a1 b1 c1 d1 : Real}
  {S : Set V}
-- given
  (ha : a1 ≤ a0)
  (hb : b0 ≤ b1)
  (hc : c0 ≤ c1)
  (hd : d1 ≤ d0)
  (hS : S ⊆ E.rectVertices a0 b0 c1 d1) :
-- imply
  P.setHitsInfinite S ⊆ E.rectSideConnectionEvent a1 b1 c1 d1 S (E.rectBottomBoundaryVertices a1 b1 c1 d1) ∪ (E.rectSideConnectionEvent a1 b1 c1 d1 S (E.rectTopBoundaryVertices a1 b1 c1 d1) ∪ (E.rectSideConnectionEvent a0 b0 c0 d0 S (E.rectLeftBoundaryVertices a0 b0 c0 d0) ∪ E.rectSideConnectionEvent a0 b0 c0 d0 S (E.rectRightBoundaryVertices a0 b0 c0 d0))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.setHitsInfinite_subset_mixedRectSideConnection_union E a0 b0 c0 d0 a1 b1 c1 d1 S ha hb hc hd hS

/--
[PeriodicPlaneEmbedding.preference_mixed_max_add_epsilon_ge_fourthRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma preference_mixed_max_add_epsilon_ge_fourthRoot_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a0 b0 c0 d0 a1 b1 c1 d1 : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hepsilon : 0 ≤ epsilon)
  (ha : a1 ≤ a0)
  (hb : b0 ≤ b1)
  (hc : c0 ≤ c1)
  (hd : d1 ≤ d0)
  (hS : S ⊆ E.rectVertices a0 b0 c1 d1)
  (hBottomTop : mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S (E.rectTopBoundaryVertices a1 b1 c1 d1)) ≤ mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S (E.rectBottomBoundaryVertices a1 b1 c1 d1)) + epsilon)
  (hLeftRight : mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S (E.rectRightBoundaryVertices a0 b0 c0 d0)) ≤ mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S (E.rectLeftBoundaryVertices a0 b0 c0 d0)) + epsilon) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤ max (mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S (E.rectBottomBoundaryVertices a1 b1 c1 d1))) (mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S (E.rectLeftBoundaryVertices a0 b0 c0 d0))) + epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preference_mixed_max_add_epsilon_ge_fourthRoot E mu hFKG a0 b0 c0 d0 a1 b1 c1 d1 S epsilon hepsilon ha hb hc hd hS hBottomTop hLeftRight

/--
[PeriodicPlaneEmbedding.exists_mixed_approxPreferredSide_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_mixed_approxPreferredSide_crossing_branch_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a0 b0 c0 d0 a1 b1 c1 d1 : Real}
  {width height : Nat}
  {epsilon : Real}
  {source : PreferenceGridVertex width height → Finset V}
  {bottom top left right : PreferenceGridVertex width height → Real}
-- given
  (hFKG : IsFKG mu)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hepsilon : 0 ≤ epsilon)
  (ha : a1 ≤ a0)
  (hb : b0 ≤ b1)
  (hc : c0 ≤ c1)
  (hd : d1 ≤ d0)
  (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a0 b0 c1 d1)
  (hbottomScore : ∀ x, bottom x = mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V) (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
  (htopScore : ∀ x, top x = mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V) (E.rectTopBoundaryVertices a1 b1 c1 d1)))
  (hleftScore : ∀ x, left x = mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V) (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
  (hrightScore : ∀ x, right x = mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V) (E.rectRightBoundaryVertices a0 b0 c0 d0)))
  (hbottom : ∀ i : Fin (width + 1), top (i, 0) ≤ bottom (i, 0) + epsilon)
  (htop : ∀ i : Fin (width + 1), bottom (i, Fin.last height) ≤ top (i, Fin.last height) + epsilon)
  (hleft : ∀ j : Fin (height + 1), right (0, j) ≤ left (0, j) + epsilon)
  (hright : ∀ j : Fin (height + 1), left (Fin.last width, j) ≤ right (Fin.last width, j) + epsilon) :
-- imply
  ∃ x xVertical xHorizontal : PreferenceGridVertex width height, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ bottom x + epsilon ∧ bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 d1 (source x) (source xVertical)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 d1 (source x) (source xVertical)) ≤ mu.real (E.verticalCrossingEvent a1 b1 c1 d1)) ∨ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ left x + epsilon ∧ left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - mu.real (E.rectanglePairMergeErrorUnion a0 b0 c0 d0 (source x) (source xHorizontal)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a0 b0 c0 d0 (source x) (source xHorizontal)) ≤ mu.real (E.horizontalCrossingEvent a0 b0 c0 d0))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_mixed_approxPreferredSide_crossing_branch E mu hFKG a0 b0 c0 d0 a1 b1 c1 d1 hwidth hheight epsilon hepsilon source bottom top left right ha hb hc hd hsource hbottomScore htopScore hleftScore hrightScore hbottom htop hleft hright

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_mixedGridPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_uniformTemplate_mixedGridPreference_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real), Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) → (∀ n, a1 n ≤ a0 n) → (∀ n, b0 n ≤ b1 n) → (∀ n, c0 n ≤ c1 n) → (∀ n, d1 n ≤ d0 n) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) → (∀ n i, top n (i, 0) ≤ bottom n (i, 0) + epsilon n) → (∀ n i, bottom n (i, Fin.last (height n)) ≤ top n (i, Fin.last (height n)) + epsilon n) → (∀ n j, right n (0, j) ≤ left n (0, j) + epsilon n) → (∀ n j, left n (Fin.last (width n), j) ≤ right n (Fin.last (width n), j) + epsilon n) → Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (a0 n) (b0 n) (c0 n) (d0 n))) (mu.real (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n) (d1 n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_mixedGridPreference_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a0 b0 c0 d0 a1 b1 c1 d1 p : Nat → Real), Tendsto p atTop (nhds 1) → (∀ n, p n ≤ 1) → (∀ n, a1 n ≤ a0 n) → (∀ n, b0 n ≤ b1 n) → (∀ n, c0 n ≤ c1 n) → (∀ n, d1 n ≤ d0 n) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n)) → (∀ n (i : Fin (width n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite (i, (0 : Fin (height n + 1))))) : Set V) (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) → (∀ n (i : Fin (width n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite (i, Fin.last (height n)))) : Set V) (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) → (∀ n (j : Fin (height n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite ((0 : Fin (width n + 1)), j))) : Set V) (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) → (∀ n (j : Fin (height n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite (Fin.last (width n), j))) : Set V) (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) → Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (a0 n) (b0 n) (c0 n) (d0 n))) (mu.real (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n) (d1 n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit

/--
[PeriodicPlaneEmbedding.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height margin : Nat → Nat) (base : Nat → Site 2) (a b c d p : Nat → Real), (∀ n, 2 * margin n < width n) → (∀ n, 2 * margin n < height n) → (∀ n, p n ≤ 1) → Tendsto p atTop (nhds 1) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((P.orbitBox n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), margin n ≤ v.1.val → v.1.val + margin n < width n → margin n ≤ v.2.val → v.2.val + margin n < height n → (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), v.2.val ≤ margin n → p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (v : PreferenceGridVertex (width n) (height n)), height n ≤ v.2.val + margin n → p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (v : PreferenceGridVertex (width n) (height n)), v.1.val ≤ margin n → p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (v : PreferenceGridVertex (width n) (height n)), width n ≤ v.1.val + margin n → p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one E mu hFKG hTI hunique

/--
[PeriodicPlanarDualPair.TwoLevelRectangleArray.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean)
-/
@[path]
private lemma false_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {data : D.TwoLevelRectangleArray mu B} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.TwoLevelRectangleArray.false D mu data


-- created on 2026-10-23
