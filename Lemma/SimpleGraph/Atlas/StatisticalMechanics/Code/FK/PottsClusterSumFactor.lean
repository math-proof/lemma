import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsClusterSumFactor
open MeasureTheory Set StatMech StatMech.FK


/--
[pottsClusterSumSpin_eq_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumSpin_eq_of_connected_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (label : Site d -> Fin q)
  (hxy : Connected d omega x y) :
-- imply
  pottsClusterSumSpin boundaryColor omega label x = pottsClusterSumSpin boundaryColor omega label y := by
-- proof
  apply StatMech.FK.pottsClusterSumSpin_eq_of_connected boundaryColor omega label hxy

/--
[pottsClusterSumSpin_constOnOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumSpin_constOnOpen_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
-- given
  (label : Site d -> Fin q) :
-- imply
  ConstOnOpen (hypercubicLattice d) omega (pottsClusterSumSpin boundaryColor omega label) := by
-- proof
  apply StatMech.FK.pottsClusterSumSpin_constOnOpen boundaryColor omega label

/--
[pottsClusterSumSpin_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumSpin_of_infinite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (label : Site d -> Fin q)
  (hinfinite : (cluster d omega x).Infinite) :
-- imply
  pottsClusterSumSpin boundaryColor omega label x = boundaryColor := by
-- proof
  apply StatMech.FK.pottsClusterSumSpin_of_infinite boundaryColor omega label x hinfinite

/--
[pottsClusterSumSpin_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumSpin_of_finite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (label : Site d -> Fin q)
  (hfinite : (cluster d omega x).Finite) :
-- imply
  pottsClusterSumSpin boundaryColor omega label x = ∑ y ∈ hfinite.toFinset, label y := by
-- proof
  apply StatMech.FK.pottsClusterSumSpin_of_finite boundaryColor omega label x hfinite

/--
[pottsClusterSumSpin_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumSpin_shift_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {g : Multiplicative (Site d)}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (label : Site d -> Fin q) :
-- imply
  pottsClusterSumSpin boundaryColor (ConfigSpace.shift g omega) (pottsLabelShift g label) (g • x) = pottsClusterSumSpin boundaryColor omega label x := by
-- proof
  apply StatMech.FK.pottsClusterSumSpin_shift boundaryColor g omega label x

/--
[sum_pottsLabelTwist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma sum_pottsLabelTwist_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : Nat}
  [NeZero q]
  {root : ι}
  {increment : Fin q}
-- given
  (label : ι -> Fin q) :
-- imply
  ∑ i, pottsLabelTwist root increment label i = (∑ i, label i) + increment := by
-- proof
  apply StatMech.FK.sum_pottsLabelTwist root increment label

/--
[card_pottsClusterSumFiber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma card_pottsClusterSumFiber_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {q : Nat}
  [NeZero q]
  {a b : Fin q} :
-- imply
  Fintype.card {label : ι -> Fin q // ∑ i, label i = a} = Fintype.card {label : ι -> Fin q // ∑ i, label i = b} := by
-- proof
  apply StatMech.FK.card_pottsClusterSumFiber_eq a b

/--
[card_pottsClusterSumFiber_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma card_pottsClusterSumFiber_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {q : Nat}
  [NeZero q]
  {a : Fin q} :
-- imply
  q * Fintype.card {label : ι -> Fin q // ∑ i, label i = a} = Fintype.card (ι -> Fin q) := by
-- proof
  apply StatMech.FK.card_pottsClusterSumFiber_mul a

/--
[pottsUniformPi_eq_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsUniformPi_eq_uniform_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : Nat}
  [NeZero q] :
-- imply
  Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) = (PMF.uniformOfFintype (ι -> Fin q)).toMeasure := by
-- proof
  apply StatMech.FK.pottsUniformPi_eq_uniform

/--
[pottsUniformPi_sum_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsUniformPi_sum_apply_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {q : Nat}
  [NeZero q]
  {a : Fin q} :
-- imply
  Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) {label | ∑ i, label i = a} = (q : ENNReal)⁻¹ := by
-- proof
  apply StatMech.FK.pottsUniformPi_sum_apply a

/--
[pottsUniformPi_sum_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsUniformPi_sum_map_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {q : Nat}
  [NeZero q] :
-- imply
  Measure.map (fun label : ι -> Fin q => ∑ i, label i) (Measure.pi fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) = (PMF.uniformOfFintype (Fin q)).toMeasure := by
-- proof
  apply StatMech.FK.pottsUniformPi_sum_map

/--
[pottsIID_blockLabels_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsIID_blockLabels_law_eq
  [DecidableEq ι]
  {q : Nat}
  [NeZero q]
-- given
  (F : κ -> Finset ι)
  (hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l)) :
-- imply
  Measure.map (pottsBlockLabels F) (Measure.infinitePi fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) = Measure.infinitePi fun k : κ => Measure.infinitePi fun _ : F k => (PMF.uniformOfFintype (Fin q)).toMeasure := by
-- proof
  apply StatMech.FK.pottsIID_blockLabels_law F hdisjoint

/--
[pottsIID_blockSums_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsIID_blockSums_law_eq
  [DecidableEq ι]
  {q : Nat}
  [NeZero q]
-- given
  (F : κ -> Finset ι)
  (hF : ∀ k, (F k).Nonempty)
  (hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l)) :
-- imply
  Measure.map (pottsBlockSums F) (Measure.infinitePi fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) = Measure.infinitePi fun _ : κ => (PMF.uniformOfFintype (Fin q)).toMeasure := by
-- proof
  apply StatMech.FK.pottsIID_blockSums_law F hF hdisjoint

/--
[pottsClusterSumJointFactor_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumJointFactor_shift_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {g : Multiplicative (Site d)}
-- given
  (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :
-- imply
  pottsClusterSumJointFactor boundaryColor (pottsClusterFactorInputShift g input) = pottsJointShift g (pottsClusterSumJointFactor boundaryColor input) := by
-- proof
  apply StatMech.FK.pottsClusterSumJointFactor_shift boundaryColor g input

/--
[measurableSet_pottsClusterEqEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma measurableSet_pottsClusterEqEvent_eq
  {d : Nat}
  {x : Site d}
  {F : Finset (Site d)} :
-- imply
  MeasurableSet (pottsClusterEqEvent d x F) := by
-- proof
  apply StatMech.FK.measurableSet_pottsClusterEqEvent d x F

/--
[measurableSet_pottsLabelSumEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma measurableSet_pottsLabelSumEvent_eq
  {d q : Nat}
  [NeZero q]
  {F : Finset (Site d)}
  {a : Fin q} :
-- imply
  MeasurableSet (pottsLabelSumEvent F a) := by
-- proof
  apply StatMech.FK.measurableSet_pottsLabelSumEvent F a

/--
[measurableSet_pottsClusterSumFiberEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma measurableSet_pottsClusterSumFiberEvent_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {x : Site d}
  {a : Fin q} :
-- imply
  MeasurableSet (pottsClusterSumFiberEvent boundaryColor x a) := by
-- proof
  apply StatMech.FK.measurableSet_pottsClusterSumFiberEvent boundaryColor x a

/--
[pottsClusterSumFiberEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumFiberEvent_eq_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {x : Site d}
  {a : Fin q} :
-- imply
  pottsClusterSumFiberEvent boundaryColor x a = {input | pottsClusterSumSpin boundaryColor input.1 input.2 x = a} := by
-- proof
  apply StatMech.FK.pottsClusterSumFiberEvent_eq boundaryColor x a

/--
[measurable_pottsClusterSumSpin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma measurable_pottsClusterSumSpin_apply_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {x : Site d} :
-- imply
  Measurable (fun input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) => pottsClusterSumSpin boundaryColor input.1 input.2 x) := by
-- proof
  apply StatMech.FK.measurable_pottsClusterSumSpin_apply boundaryColor x

/--
[measurable_pottsClusterSumSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma measurable_pottsClusterSumSpin_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q} :
-- imply
  Measurable (fun input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) => pottsClusterSumSpin boundaryColor input.1 input.2) := by
-- proof
  apply StatMech.FK.measurable_pottsClusterSumSpin boundaryColor

/--
[measurable_pottsClusterSumJointFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma measurable_pottsClusterSumJointFactor_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q} :
-- imply
  Measurable (pottsClusterSumJointFactor boundaryColor : (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) -> ((Site d -> Fin q) × ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.measurable_pottsClusterSumJointFactor boundaryColor

/--
[pottsIIDLabelMeasure_pottsLabelSumEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsIIDLabelMeasure_pottsLabelSumEvent_eq
  {d q : Nat}
  [NeZero q]
  {F : Finset (Site d)}
  {a : Fin q}
-- given
  (hF : F.Nonempty) :
-- imply
  pottsIIDLabelMeasure d q (pottsLabelSumEvent F a) = (q : ENNReal)⁻¹ := by
-- proof
  apply StatMech.FK.pottsIIDLabelMeasure_pottsLabelSumEvent F hF a

/--
[pottsClusterSumSpin_representatives_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumSpin_representatives_law_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
-- given
  (r : κ -> Site d)
  (hfinite : ∀ k, (cluster d omega (r k)).Finite)
  (hdistinct : ∀ k l, k ≠ l -> ¬Connected d omega (r k) (r l)) :
-- imply
  Measure.map (fun label k => pottsClusterSumSpin boundaryColor omega label (r k)) (pottsIIDLabelMeasure d q) = Measure.infinitePi fun _ : κ => (PMF.uniformOfFintype (Fin q)).toMeasure := by
-- proof
  apply StatMech.FK.pottsClusterSumSpin_representatives_law boundaryColor omega r hfinite hdistinct

/--
[pottsClusterSumJointMeasure_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_isProbabilityMeasure_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure edgeMeasure] :
-- imply
  IsProbabilityMeasure (pottsClusterSumJointMeasure boundaryColor edgeMeasure) := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_isProbabilityMeasure boundaryColor edgeMeasure

/--
[pottsClusterSumJointMeasure_map_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_map_snd_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure edgeMeasure] :
-- imply
  Measure.map Prod.snd (pottsClusterSumJointMeasure boundaryColor edgeMeasure) = edgeMeasure := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_map_snd boundaryColor edgeMeasure


-- created on 2026-10-23
