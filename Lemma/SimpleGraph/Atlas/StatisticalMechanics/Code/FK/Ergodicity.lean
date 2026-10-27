import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
open MeasureTheory ProbabilityTheory MeasurableSpace StatMech StatMech.FK


/--
[bernoulli_iIndepFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma bernoulli_iIndepFun_eq
  [Group G]
  [MulAction G E]
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  iIndepFun (fun (e : E) (ω : ConfigSpace E) => ω e) (bernoulliProductMeasure (E := E) p hp) := by
-- proof
  apply StatMech.FK.bernoulli_iIndepFun p hp

/--
[bernoulli_cylinder_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma bernoulli_cylinder_factor_eq
  [Group G]
  [MulAction G E]
  {s t : Finset E}
  {S : Set (Π i : s, Bool)}
  {T : Set (Π i : t, Bool)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hS : MeasurableSet S)
  (hT : MeasurableSet T)
  (hd : Disjoint s t) :
-- imply
  bernoulliProductMeasure (E := E) p hp (cylinder s S ∩ cylinder t T) = bernoulliProductMeasure (E := E) p hp (cylinder s S) * bernoulliProductMeasure (E := E) p hp (cylinder t T) := by
-- proof
  apply StatMech.FK.bernoulli_cylinder_factor p hp hS hT hd

/--
[exists_disjoint_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma exists_disjoint_translate_eq
  [Group G]
  [MulAction G E]
  [Infinite G]
  {s t : Finset E}
-- given
  (hfin : ∀ a b : E, {g : G | g • a = b}.Finite) :
-- imply
  ∃ g : G, Disjoint (s : Set E) (g⁻¹ • (t : Set E)) := by
-- proof
  apply StatMech.FK.exists_disjoint_translate hfin s t

/--
[finite_solution_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma finite_solution_of_injective_eq
  [Group G]
  [MulAction G E]
  {a b : E}
-- given
  (hinj : ∀ a : E, Function.Injective (fun g : G => g • a)) :
-- imply
  {g : G | g • a = b}.Finite := by
-- proof
  apply StatMech.FK.finite_solution_of_injective hinj a b

/--
[shift_preimage_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma shift_preimage_cylinder_eq
  [Group G]
  [MulAction G E]
  [DecidableEq E]
  {g : G}
  {t : Finset E}
  {T : Set (Π i : t, Bool)} :
-- imply
  (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (cylinder t T) = cylinder (t.image (fun e => g⁻¹ • e)) ((fun (x : Π i : (t.image (fun e => g⁻¹ • e)), Bool) (i : t) => x ⟨g⁻¹ • (i : E), Finset.mem_image_of_mem _ i.2⟩) ⁻¹' T) := by
-- proof
  apply StatMech.FK.shift_preimage_cylinder g t T

/--
[bernoulli_mixing_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma bernoulli_mixing_cylinder_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  [DecidableEq E]
  [Infinite G]
  {s t : Finset E}
  {S : Set (Π i : s, Bool)}
  {T : Set (Π i : t, Bool)}
-- given
  (hfin : ∀ a b : E, {g : G | g • a = b}.Finite)
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hS : MeasurableSet S)
  (hT : MeasurableSet T) :
-- imply
  ∃ g : G, bernoulliProductMeasure (E := E) p hp (cylinder s S ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' cylinder t T) = bernoulliProductMeasure (E := E) p hp (cylinder s S) * bernoulliProductMeasure (E := E) p hp (cylinder t T) := by
-- proof
  apply StatMech.FK.bernoulli_mixing_cylinder hfin p hp s t S T hS hT

/--
[isSetRing_measurableCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma isSetRing_measurableCylinders_eq
  [Group G]
  [MulAction G E] :
-- imply
  IsSetRing (measurableCylinders (fun _ : E => Bool)) := by
-- proof
  apply StatMech.FK.isSetRing_measurableCylinders

/--
[generateFrom_cylinders_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma generateFrom_cylinders_eq_eq
  [Group G]
  [MulAction G E] :
-- imply
  (inferInstance : MeasurableSpace (ConfigSpace E)) = generateFrom (measurableCylinders (fun _ : E => Bool)) := by
-- proof
  apply StatMech.FK.generateFrom_cylinders_eq

/--
[exists_cylinder_symmDiff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma exists_cylinder_symmDiff_lt_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  {A : Set (ConfigSpace E)}
  {ε : ℝ≥0∞}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hA : MeasurableSet A)
  (hε : 0 < ε) :
-- imply
  ∃ C ∈ measurableCylinders (fun _ : E => Bool), bernoulliProductMeasure (E := E) p hp (C ∆ A) < ε := by
-- proof
  apply StatMech.FK.exists_cylinder_symmDiff_lt p hp hA hε

/--
[bernoulli_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma bernoulli_ergodic_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  [Infinite G]
  {s : Set (ConfigSpace E)}
-- given
  (hfin : ∀ a b : E, {g : G | g • a = b}.Finite)
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  bernoulliProductMeasure (E := E) p hp s = 0 ∨ bernoulliProductMeasure (E := E) p hp s = bernoulliProductMeasure (E := E) p hp Set.univ := by
-- proof
  apply StatMech.FK.bernoulli_ergodic hfin p hp hs hinv

/--
[bernoulli_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean)
-/
@[path]
private lemma bernoulli_isErgodic_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  [Infinite G]
-- given
  (hinj : ∀ a : E, Function.Injective (fun g : G => g • a))
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  ConfigSpace.IsErgodic (G := G) (bernoulliProductMeasure (E := E) p hp) := by
-- proof
  apply StatMech.FK.bernoulli_isErgodic hinj p hp


-- created on 2026-10-23
