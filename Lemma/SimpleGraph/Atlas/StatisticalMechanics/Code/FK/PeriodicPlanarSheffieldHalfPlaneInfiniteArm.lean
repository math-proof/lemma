import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.infiniteSetConnectionWithin_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteSetConnectionWithin_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T : Set V} :
-- imply
  MeasurableSet (P.infiniteSetConnectionWithin A S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteSetConnectionWithin_measurableSet P A S T

/--
[PeriodicGraph.infiniteSetConnectionWithin_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteSetConnectionWithin_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T : Set V} :
-- imply
  IsIncreasing (P.infiniteSetConnectionWithin A S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteSetConnectionWithin_isIncreasing P A S T

/--
[PeriodicGraph.infiniteSetConnectionWithin_mono_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteSetConnectionWithin_mono_target_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S : Set V}
  {T U : Set V}
-- given
  (hTU : T ⊆ U) :
-- imply
  P.infiniteSetConnectionWithin A S T ⊆ P.infiniteSetConnectionWithin A S U := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteSetConnectionWithin_mono_target P A S hTU

/--
[PeriodicGraph.infiniteSetConnectionWithin_union_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteSetConnectionWithin_union_target_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T U : Set V} :
-- imply
  P.infiniteSetConnectionWithin A S (T ∪ U) = P.infiniteSetConnectionWithin A S T ∪ P.infiniteSetConnectionWithin A S U := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteSetConnectionWithin_union_target P A S T U

/--
[PeriodicGraph.infiniteSetConnectionWithin_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteSetConnectionWithin_configTranslate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {A S T : Set V} :
-- imply
  P.configTranslate z omega ∈ P.infiniteSetConnectionWithin (P.shift z '' A) (P.shift z '' S) (P.shift z '' T) ↔ omega ∈ P.infiniteSetConnectionWithin A S T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteSetConnectionWithin_configTranslate P z omega A S T

/--
[PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteBoundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma unique_two_sides_subset_infiniteBoundaryConnection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : ℝ}
  {S T : Set V}
-- given
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩ (P.setHitsInfinite S ∩ P.setHitsInfinite T) ⊆ P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteBoundaryConnection E r hS hT

/--
[PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteBoundaryConnection_measureReal_ge_mul_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {S T : Set V}
-- given
  (hFKG : IsFKG mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  mu.real (P.setHitsInfinite S) * mu.real (P.setHitsInfinite T) ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_mul E mu hFKG hunique r hS hT

/--
[PeriodicGraph.infiniteSetConnectionWithin_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteSetConnectionWithin_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {A S T : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.infiniteSetConnectionWithin (P.shift z '' A) (P.shift z '' S) (P.shift z '' T)) = mu.real (P.infiniteSetConnectionWithin A S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteSetConnectionWithin_translate_measureReal_eq P mu hTI z A S T

/--
[PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_sq_of_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteBoundaryConnection_measureReal_ge_sq_of_translate_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {S : Set V}
  {z : Site 2}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : P.shift z '' S ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  (mu.real (P.setHitsInfinite S)) ^ 2 ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_sq_of_translate E mu hFKG hTI hunique r S z hS hT

/--
[PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {N : Nat}
  {z₀ : Site 2}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hinside : P.shift z₀ '' (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices r) :
-- imply
  (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift z₀ '' (P.orbitBox N : Set V)) (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift E mu hFKG hTI hunique r N z₀ hinside

/--
[PeriodicPlaneEmbedding.exists_infiniteBoundaryConnection_sequence_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_infiniteBoundaryConnection_sequence_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ S : ℕ → Set V, (∀ N, (S N).Finite) ∧ (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧ Tendsto (fun N => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (S N) (E.rightHalfPlaneBoundaryVertices r))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_infiniteBoundaryConnection_sequence_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteLowerBoundaryRay_connection_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono E r S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma iUnion_infiniteLowerBoundaryRay_connection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r n)) = P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection E r S

/--
[PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteLowerBoundaryRay_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r n))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto E mu r S

/--
[PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteUpperBoundaryRay_connection_mono_neg_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (-(n : Real)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_neg E r S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma iUnion_infiniteUpperBoundaryRay_connection_neg_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (-(n : Real)))) = P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_neg E r S

/--
[PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteUpperBoundaryRay_measureReal_tendsto_neg_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (-(n : Real))))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_neg E mu r S

/--
[PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteLowerBoundaryRay_connection_mono_add_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r (s + n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono_add E r s S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma iUnion_infiniteLowerBoundaryRay_connection_add_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r (s + n))) = P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection_add E r s S

/--
[PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteLowerBoundaryRay_measureReal_tendsto_add_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r (s + n)))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto_add E mu r s S

/--
[PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteUpperBoundaryRay_connection_mono_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (s - n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_sub E r s S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma iUnion_infiniteUpperBoundaryRay_connection_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (s - n))) = P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_sub E r s S

/--
[PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteUpperBoundaryRay_measureReal_tendsto_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (s - n)))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_sub E mu r s S

/--
[PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteLowerBoundaryRay_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S) (E.lowerBoundaryRayVertices r (s + t))) = mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_vertical E mu hTI t r s S

/--
[PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteUpperBoundaryRay_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S) (E.upperBoundaryRayVertices r (s + t))) = mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_vertical E mu hTI t r s S

/--
[PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteBoundaryConnection_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S) (E.rightHalfPlaneBoundaryVertices r)) = mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_vertical E mu hTI t r S

/--
[PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteLowerBoundaryRay_measureReal_ge_sqrt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {S : Set V}
-- given
  (hFKG : IsFKG mu)
  (hpref : mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))) :
-- imply
  1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt E mu hFKG r s S hpref

/--
[PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteUpperBoundaryRay_measureReal_ge_sqrt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {S : Set V}
-- given
  (hFKG : IsFKG mu)
  (hpref : mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))) :
-- imply
  1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt E mu hFKG r s S hpref

/--
[PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteLowerBoundaryRay_measureReal_ge_sqrt_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hepsilon : 0 ≤ epsilon)
  (hpref : mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) + epsilon) :
-- imply
  1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt_sub E mu hFKG r s S hepsilon hpref

/--
[PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma infiniteUpperBoundaryRay_measureReal_ge_sqrt_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hepsilon : 0 ≤ epsilon)
  (hpref : mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) + epsilon) :
-- imply
  1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt_sub E mu hFKG r s S hepsilon hpref

/--
[PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (-(n : Int))) '' S) (E.lowerBoundaryRayVertices r 0))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto E mu hTI r S

/--
[PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (n : Int)) '' S) (E.upperBoundaryRayVertices r 0))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto E mu hTI r S

/--
[PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_at_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (-(n : Int))) '' S) (E.lowerBoundaryRayVertices r s))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_at E mu hTI r s S

/--
[PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_at_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (n : Int)) '' S) (E.upperBoundaryRayVertices r s))) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_at E mu hTI r s S

/--
[PeriodicPlaneEmbedding.exists_finite_infiniteBoundaryConnection_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_finite_infiniteBoundaryConnection_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ S : Set V, S.Finite ∧ S ⊆ E.rightHalfPlaneVertices r ∧ 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finite_infiniteBoundaryConnection_measureReal_gt E mu hFKG hTI hunique r hepsilon

/--
[PeriodicPlaneEmbedding.exists_finite_opposite_infiniteBoundaryRays_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_finite_opposite_infiniteBoundaryRays_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L R : Set V, L.Finite ∧ R.Finite ∧ L ⊆ E.rightHalfPlaneVertices r ∧ R ⊆ E.rightHalfPlaneVertices r ∧ 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) L (E.lowerBoundaryRayVertices r 0)) ∧ 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) R (E.upperBoundaryRayVertices r 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finite_opposite_infiniteBoundaryRays_measureReal_gt E mu hFKG hTI hunique r hepsilon

/--
[exists_adjacent_preference_crossover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_adjacent_preference_crossover_eq
  [DecidableEq V]
  [Countable V]
  {lower upper : Nat → Real}
  {a k : Nat}
-- given
  (hstart : upper a ≤ lower a)
  (hend : lower (a + k + 1) ≤ upper (a + k + 1)) :
-- imply
  ∃ t : Nat, a ≤ t ∧ t < a + k + 1 ∧ upper t ≤ lower t ∧ lower (t + 1) ≤ upper (t + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_adjacent_preference_crossover lower upper a k hstart hend

/--
[exists_adjacent_approximate_preference_crossover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_adjacent_approximate_preference_crossover_eq
  [DecidableEq V]
  [Countable V]
  {lower upper : Nat → Real}
  {epsilon : Real}
  {a k : Nat}
-- given
  (hepsilon : 0 ≤ epsilon)
  (hstart : upper a ≤ lower a + epsilon)
  (hend : lower (a + k + 1) ≤ upper (a + k + 1) + epsilon) :
-- imply
  ∃ t : Nat, a ≤ t ∧ t < a + k + 1 ∧ upper t ≤ lower t + epsilon ∧ lower (t + 1) ≤ upper (t + 1) + epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_adjacent_approximate_preference_crossover lower upper epsilon a k hepsilon hstart hend

/--
[verticalShift_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma verticalShift_add_eq
  [DecidableEq V]
  [Countable V]
  {a b : Int} :
-- imply
  verticalShift (a + b) = verticalShift a + verticalShift b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.verticalShift_add a b

/--
[PeriodicGraph.shift_image_vertical_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma shift_image_vertical_add_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {a b : Int}
  {S : Set V} :
-- imply
  P.shift (verticalShift b) '' (P.shift (verticalShift a) '' S) = P.shift (verticalShift (a + b)) '' S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shift_image_vertical_add P a b S

/--
[PeriodicPlaneEmbedding.exists_adjacent_infiniteBoundaryRays_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_adjacent_infiniteBoundaryRays_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Int, 1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift z) '' S) (E.lowerBoundaryRayVertices r s)) ∧ 1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (z + 1)) '' S) (E.upperBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_adjacent_infiniteBoundaryRays_measureReal_ge E mu hFKG hTI r s S hepsilon

/--
[PeriodicPlaneEmbedding.exists_twoStep_infiniteBoundaryRays_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_twoStep_infiniteBoundaryRays_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Int, 1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift z) '' S) (E.lowerBoundaryRayVertices r 0)) ∧ 1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (z + 2)) '' S) (E.upperBoundaryRayVertices r 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_twoStep_infiniteBoundaryRays_measureReal_ge E mu hFKG hTI r S hepsilon

/--
[PeriodicPlaneEmbedding.exists_separated_infiniteBoundaryRays_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInfiniteArm.lean)
-/
@[path]
private lemma exists_separated_infiniteBoundaryRays_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {t : Int}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Int, 1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift z) '' S) (E.lowerBoundaryRayVertices r s)) ∧ 1 - Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (z + 1 + t)) '' S) (E.upperBoundaryRayVertices r (s + t))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_separated_infiniteBoundaryRays_measureReal_ge E mu hFKG hTI r s t S hepsilon


-- created on 2026-10-23
