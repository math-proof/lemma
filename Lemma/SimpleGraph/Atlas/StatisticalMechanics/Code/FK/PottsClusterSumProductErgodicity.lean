import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity.Part3
open Filter Function MeasureTheory MeasurableSpace Set Topology StatMech StatMech.FK


/--
[ergodic_prod_of_mixingAgainst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma ergodic_prod_of_mixingAgainst_eq
  [MeasurableSpace Alpha]
  [MeasurableSpace Beta]
  {mu : Measure Alpha}
  {nu : Measure Beta}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
  {D : Set (Set Beta)}
-- given
  (T : Alpha -> Alpha)
  (S : Beta -> Beta)
  (hT : _root_.Ergodic T mu)
  (hS : MeasurePreserving S nu nu)
  (hDgen : generateFrom D = (inferInstance : MeasurableSpace Beta))
  (hDpi : IsPiSystem D)
  (hDspan : IsCountablySpanning D)
  (hDmeas : forall B, B ∈ D -> MeasurableSet B)
  (hmix : MixingAgainst S nu D) :
-- imply
  _root_.Ergodic (Prod.map T S) (mu.prod nu) := by
-- proof
  apply StatMech.FK.ergodic_prod_of_mixingAgainst T S hT hS D hDgen hDpi hDspan hDmeas hmix

/--
[pottsLabelShift_eq_piCongrLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsLabelShift_eq_piCongrLeft_eq
  {d q : Nat}
  {g : Multiplicative (Site d)} :
-- imply
  (pottsLabelShift g : (Site d -> Fin q) -> (Site d -> Fin q)) = ⇑(Equiv.piCongrLeft (fun _ : Site d => Fin q) (MulAction.toPerm g)) := by
-- proof
  apply StatMech.FK.pottsLabelShift_eq_piCongrLeft g

/--
[pottsIIDLabelMeasure_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsIIDLabelMeasure_measurePreserving_eq
  {d q : Nat}
  [NeZero q]
  {g : Multiplicative (Site d)} :
-- imply
  MeasurePreserving (pottsLabelShift g) (pottsIIDLabelMeasure d q) (pottsIIDLabelMeasure d q) := by
-- proof
  apply StatMech.FK.pottsIIDLabelMeasure_measurePreserving g

/--
[pottsLabelShift_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsLabelShift_mul_eq
  {d q : Nat}
-- given
  (g h : Multiplicative (Site d)) :
-- imply
  (pottsLabelShift (g * h) : (Site d -> Fin q) -> (Site d -> Fin q)) = pottsLabelShift g ∘ pottsLabelShift h := by
-- proof
  apply StatMech.FK.pottsLabelShift_mul g h

/--
[pottsLabelShift_freeAxisTranslationPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsLabelShift_freeAxisTranslationPower_eq
  {d q : Nat}
  {n : Nat}
-- given
  (hd : 1 <= d) :
-- imply
  (pottsLabelShift (freeAxisTranslationPower hd n) : (Site d -> Fin q) -> (Site d -> Fin q)) = (pottsLabelShift (freeAxisTranslation hd))^[n] := by
-- proof
  apply StatMech.FK.pottsLabelShift_freeAxisTranslationPower hd n

/--
[pottsLabelShift_preimage_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsLabelShift_preimage_cylinder_eq
  {d q : Nat}
  {g : Multiplicative (Site d)}
  {t : Finset (Site d)}
-- given
  (T : Set (t -> Fin q)) :
-- imply
  (pottsLabelShift g : (Site d -> Fin q) -> (Site d -> Fin q)) ⁻¹' cylinder t T = cylinder (t.image (fun x => g⁻¹ • x)) ((fun (label : (t.image (fun x => g⁻¹ • x)) -> Fin q) (x : t) => label ⟨g⁻¹ • (x : Site d), Finset.mem_image_of_mem _ x.2⟩) ⁻¹' T) := by
-- proof
  apply StatMech.FK.pottsLabelShift_preimage_cylinder g t T

/--
[pottsIIDLabel_axis_mixingAgainst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsIIDLabel_axis_mixingAgainst_eq
  {d q : Nat}
  [NeZero q]
-- given
  (hd : 1 <= d) :
-- imply
  MixingAgainst (pottsLabelShift (freeAxisTranslation hd)) (pottsIIDLabelMeasure d q) (measurableCylinders (fun _ : Site d => Fin q)) := by
-- proof
  apply StatMech.FK.pottsIIDLabel_axis_mixingAgainst hd

/--
[freeInfiniteVolume_axisShift_ergodic_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma freeInfiniteVolume_axisShift_ergodic_generalQ_eq
  {d : Nat}
  {p q : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  _root_.Ergodic (ConfigSpace.shift (freeAxisTranslation hd) : ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d))) (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_axisShift_ergodic_generalQ hd hp hp1 hq

/--
[freeInfiniteVolume_prod_pottsIIDLabel_axis_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma freeInfiniteVolume_prod_pottsIIDLabel_axis_ergodic_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) _root_.Ergodic (Prod.map (ConfigSpace.shift (freeAxisTranslation hd) : ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d))) (pottsLabelShift (freeAxisTranslation hd))) ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod (pottsIIDLabelMeasure d q)) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_prod_pottsIIDLabel_axis_ergodic hd hp hp1

/--
[freeInfiniteVolume_pottsClusterFactorInput_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma freeInfiniteVolume_pottsClusterFactorInput_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) IsErgodicFor pottsClusterFactorInputShift ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod (pottsIIDLabelMeasure d q)) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_pottsClusterFactorInput_isErgodicFor hd hp hp1

/--
[freePottsClusterSumJointMeasure_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma freePottsClusterSumJointMeasure_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
  {boundaryColor : Fin q}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) IsErgodicFor (pottsJointShift (d := d) (q := q)) (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _)) := by
-- proof
  apply StatMech.FK.freePottsClusterSumJointMeasure_isErgodicFor hd hp hp1 boundaryColor

/--
[freePottsClusterSumSpinMarginal_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma freePottsClusterSumSpinMarginal_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
  {boundaryColor : Fin q}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) IsErgodicFor (pottsSpinShift (d := d) (q := q)) (Measure.map Prod.fst (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _))) := by
-- proof
  apply StatMech.FK.freePottsClusterSumSpinMarginal_isErgodicFor hd hp hp1 boundaryColor

/--
[measurableSet_pottsAllClustersFiniteEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma measurableSet_pottsAllClustersFiniteEvent_eq
  {d : Nat} :
-- imply
  MeasurableSet (pottsAllClustersFiniteEvent d) := by
-- proof
  apply StatMech.FK.measurableSet_pottsAllClustersFiniteEvent d

/--
[mem_pottsAllClustersFiniteEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma mem_pottsAllClustersFiniteEvent_iff_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))} :
-- imply
  omega ∈ pottsAllClustersFiniteEvent d ↔ forall x : Site d, (cluster d omega x).Finite := by
-- proof
  apply StatMech.FK.mem_pottsAllClustersFiniteEvent_iff omega

/--
[ae_pottsAllClustersFinite_of_translationInvariant_of_origin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma ae_pottsAllClustersFinite_of_translationInvariant_of_origin_zero_eq
  {d : Nat}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (htrans : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) edgeMeasure)
  (horigin : edgeMeasure {omega : ConfigSpace (Sym2 (Site d)) | (cluster d omega (Percolation.origin d)).Infinite} = 0) :
-- imply
  ∀ᵐ omega ∂edgeMeasure, omega ∈ pottsAllClustersFiniteEvent d := by
-- proof
  apply StatMech.FK.ae_pottsAllClustersFinite_of_translationInvariant_of_origin_zero edgeMeasure htrans horigin

/--
[pottsClusterSumJointFactor_eq_of_allClustersFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsClusterSumJointFactor_eq_of_allClustersFinite_eq
  {d q : Nat}
  [NeZero q]
  {a b : Fin q}
-- given
  (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
  (hfinite : input.1 ∈ pottsAllClustersFiniteEvent d) :
-- imply
  pottsClusterSumJointFactor a input = pottsClusterSumJointFactor b input := by
-- proof
  apply StatMech.FK.pottsClusterSumJointFactor_eq_of_allClustersFinite a b input hfinite

/--
[pottsClusterSumJointMeasure_eq_of_ae_allClustersFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_eq_of_ae_allClustersFinite_eq
  {d q : Nat}
  [NeZero q]
  {a b : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hfinite : ∀ᵐ omega ∂edgeMeasure, omega ∈ pottsAllClustersFiniteEvent d) :
-- imply
  pottsClusterSumJointMeasure a edgeMeasure = pottsClusterSumJointMeasure b edgeMeasure := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_eq_of_ae_allClustersFinite a b edgeMeasure hfinite


-- created on 2026-10-23
