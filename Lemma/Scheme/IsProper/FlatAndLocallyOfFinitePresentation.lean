import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false


universe u

/--
[AlgebraicGeometry_isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap.lean)
-/
@[path]
private lemma main
  {L : Type} [Field L] (A : ValuationSubring L)
  (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
  (hA : (A : Set L) ≠ Set.univ)
  (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
  (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
  (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
  (halg : ∀ a : ↥A, IsAlgebraic ↥ι.range a)
  (X₀ : (Scheme : Type 1)) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
  (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))
  (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))
  (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)
  (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)
  (X : (Scheme : Type 1)) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
  (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
  (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase) :
  -- imply
  IsProper toBase ∧ Flat toBase ∧ LocallyOfFinitePresentation toBase := by
  -- proof
  subst hiso
  refine ⟨?_, ?_, ?_⟩ <;> infer_instance


-- created on 2026-10-20
