import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part3
open Filter Set Topology Metric StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[exists_bounded_anchor_of_average_normSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean)
-/
@[path]
private lemma exists_bounded_anchor_of_average_normSq_le_eq
  {ι : Type}
  {s : Finset ι}
  {f : ι → Complex}
  {E : Real}
-- given
  (hs : s.Nonempty)
  (hE : 0 ≤ E)
  (haverage : (∑ x ∈ s, Complex.normSq (f x)) ≤ (s.card : Real) * E) :
-- imply
  ∃ x ∈ s, ‖f x‖ ≤ Real.sqrt E := by
-- proof
  apply StatMech.Universality.exists_bounded_anchor_of_average_normSq_le s hs f E hE haverage

/--
[finiteWindow_average_normSq_le_of_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean)
-/
@[path]
private lemma finiteWindow_average_normSq_le_of_embedding_eq
  {α β : Type}
  [Fintype α]
  {window : α ↪ β}
  {concrete : α → Complex}
  {abstract : β → Complex}
  {E : Real}
-- given
  (hvalue : ∀ x, abstract (window x) = concrete x)
  (haverage : (∑ x, Complex.normSq (concrete x)) ≤ (Fintype.card α : Real) * E) :
-- imply
  (∑ y ∈ Finset.univ.map window, Complex.normSq (abstract y)) ≤ ((Finset.univ.map window).card : Real) * E := by
-- proof
  apply StatMech.Universality.finiteWindow_average_normSq_le_of_embedding window concrete abstract E hvalue haverage

/--
[hasEventualCompactWindowDiameter_of_commonBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean)
-/
@[path]
private lemma hasEventualCompactWindowDiameter_of_commonBall_eq
  {A : FKIsingCaratheodoryApproximation}
-- given
  (support : ∀ n, Finset (A.M n))
  (hball : ∀ K : Set Complex, IsCompact K → K ⊆ A.U → ∃ center : Complex, ∃ R : Real, 0 ≤ R ∧ ∀ᶠ n in atTop, (∀ a ∈ support n, dist (A.medialEmbedding n a) center ≤ R) ∧ ∀ e : A.M n, (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) → dist (A.medialEmbedding n e) center ≤ R) :
-- imply
  A.HasEventualCompactWindowDiameter support := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.hasEventualCompactWindowDiameter_of_commonBall A support hball

/--
[eventualMedialBounds_of_holderInterpolation_and_averageEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean)
-/
@[path]
private lemma eventualMedialBounds_of_holderInterpolation_and_averageEnergy_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {I : A.HolderInterpolation}
-- given
  (support : ∀ n, Finset (A.M n))
  (henergy : A.HasEventualCompactAverageEnergy support) :
-- imply
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U → ∃ B : Real, ∀ᶠ n in atTop, ∀ e : A.M n, (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) → ‖@FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.eventualMedialBounds_of_holderInterpolation_and_averageEnergy A I I support henergy

/--
[scalingLimit_of_holderAverageEnergy_and_primitiveIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean)
-/
@[path]
private lemma scalingLimit_of_holderAverageEnergy_and_primitiveIm_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {I : A.HolderInterpolation}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (support : ∀ n, Finset (A.M n))
  (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
  (htarget : DifferentiableOn Complex target A.U)
  (htarget_ne : target A.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi A.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
  (henergy : A.HasEventualCompactAverageEnergy support)
  (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : Complex → Complex), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun n ↦ A.normalizedInterpolant (phi (psi n))) f atTop A.U → ∃ (P : Complex → Complex) (C : Real), DifferentiableOn Complex P A.U ∧ Set.EqOn (deriv P) (fun z ↦ f z ^ 2) A.U ∧ (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧ f A.root = target A.root) :
-- imply
  TendstoLocallyUniformlyOn A.normalizedInterpolant target atTop A.U ∧ TendstoLocallyUniformlyOn (deriv ∘ A.normalizedInterpolant) (deriv target) atTop A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.scalingLimit_of_holderAverageEnergy_and_primitiveIm A I I support target Phi hhol htarget htarget_ne hPhi hPhideriv E henergy hidentifyPrimitive


-- created on 2026-10-23
