import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicConvergence
open Filter Set Topology StatMech StatMech.Universality


/--
[isingFermionicEntireSquarePrimitive_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_zero_eq
  {f : ℂ → ℂ} :
-- imply
  isingFermionicEntireSquarePrimitive f 0 = 0 := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_zero f

/--
[isingFermionicEntireSquarePrimitive_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_hasDerivAt_eq
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  HasDerivAt (isingFermionicEntireSquarePrimitive f) (f z ^ 2) z := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_hasDerivAt hf z

/--
[isingFermionicEntireSquarePrimitive_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_differentiable_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  Differentiable ℂ (isingFermionicEntireSquarePrimitive f) := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_differentiable hf

/--
[isingFermionicEntireSquarePrimitive_im_eq_of_dense](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_im_eq_of_dense_eq
  {f Phi : ℂ → ℂ}
  {S : Set ℂ}
  {C : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hPhi : Continuous Phi)
  (hS : Dense S)
  (hEq : Set.EqOn (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im) (fun z ↦ (Phi z).im + C) S) :
-- imply
  ∀ z, (isingFermionicEntireSquarePrimitive f z).im = (Phi z).im + C := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_im_eq_of_dense hf hPhi S hS C hEq

/--
[isingFermionic_primitive_eq_add_real_of_im_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_primitive_eq_add_real_of_im_eq_eq
  {P Phi : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  {C : ℝ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hP : DifferentiableOn ℂ P U)
  (hPhi : DifferentiableOn ℂ Phi U)
  (him : ∀ z ∈ U, (P z).im = (Phi z).im + C) :
-- imply
  ∃ r : ℝ, ∀ z ∈ U, P z = Phi z + (r + C * Complex.I) := by
-- proof
  apply StatMech.Universality.isingFermionic_primitive_eq_add_real_of_im_eq P Phi U z₀ C hUopen hUconnected hz₀ hP hPhi him

/--
[isingFermionic_square_eq_of_primitive_im_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_square_eq_of_primitive_im_eq_eq
  {f target P Phi : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  {C : ℝ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hP : DifferentiableOn ℂ P U)
  (hPhi : DifferentiableOn ℂ Phi U)
  (hPderiv : Set.EqOn (deriv P) (fun z ↦ f z ^ 2) U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) U)
  (him : ∀ z ∈ U, (P z).im = (Phi z).im + C) :
-- imply
  ∀ z ∈ U, f z ^ 2 = target z ^ 2 := by
-- proof
  apply StatMech.Universality.isingFermionic_square_eq_of_primitive_im_eq f target P Phi U z₀ C hUopen hUconnected hz₀ hP hPhi hPderiv hPhideriv him

/--
[isingFermionic_squareRoot_unique_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_squareRoot_unique_of_anchor_eq
  {f target : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hf : DifferentiableOn ℂ f U)
  (htarget : DifferentiableOn ℂ target U)
  (hsquare : ∀ z ∈ U, f z ^ 2 = target z ^ 2)
  (hanchor : f z₀ = target z₀)
  (htarget_ne : target z₀ ≠ 0) :
-- imply
  Set.EqOn f target U := by
-- proof
  apply StatMech.Universality.isingFermionic_squareRoot_unique_of_anchor f target U z₀ hUopen hUconnected hz₀ hf htarget hsquare hanchor htarget_ne

/--
[isingFermionic_square_eq_of_squareDeriv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_square_eq_of_squareDeriv_eq_eq
  {f target : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hf : DifferentiableOn ℂ f U)
  (htarget : DifferentiableOn ℂ target U)
  (hderiv : Set.EqOn (deriv (fun z => f z ^ 2)) (deriv (fun z => target z ^ 2)) U)
  (hanchor : f z₀ ^ 2 = target z₀ ^ 2) :
-- imply
  ∀ z ∈ U, f z ^ 2 = target z ^ 2 := by
-- proof
  apply StatMech.Universality.isingFermionic_square_eq_of_squareDeriv_eq f target U z₀ hUopen hUconnected hz₀ hf htarget hderiv hanchor

/--
[isingFermionic_fullConvergence_of_subsequential_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_fullConvergence_of_subsequential_square_eq
  {F : ℕ → ℂ → ℂ}
  {target : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hF : ∀ n, DifferentiableOn ℂ (F n) U)
  (htarget : DifferentiableOn ℂ target U)
  (htarget_ne : target z₀ ≠ 0)
  (hcompact : StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact F U)
  (hidentify : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ → StrictMono ψ → TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U → (∀ z ∈ U, f z ^ 2 = target z ^ 2) ∧ f z₀ = target z₀) :
-- imply
  TendstoLocallyUniformlyOn F target atTop U ∧ TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
-- proof
  apply StatMech.Universality.isingFermionic_fullConvergence_of_subsequential_square F target U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne hcompact hidentify

/--
[isingFermionic_fullConvergence_of_subsequential_squareDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_fullConvergence_of_subsequential_squareDeriv_eq
  {F : ℕ → ℂ → ℂ}
  {target : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hF : ∀ n, DifferentiableOn ℂ (F n) U)
  (htarget : DifferentiableOn ℂ target U)
  (htarget_ne : target z₀ ≠ 0)
  (hcompact : StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact F U)
  (hidentifyDeriv : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ → StrictMono ψ → TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U → Set.EqOn (deriv (fun z => f z ^ 2)) (deriv (fun z => target z ^ 2)) U ∧ f z₀ = target z₀) :
-- imply
  TendstoLocallyUniformlyOn F target atTop U ∧ TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
-- proof
  apply StatMech.Universality.isingFermionic_fullConvergence_of_subsequential_squareDeriv F target U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne hcompact hidentifyDeriv

/--
[isingFermionic_fullConvergence_of_compactBounds_and_squareDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_fullConvergence_of_compactBounds_and_squareDeriv_eq
  {F : ℕ → ℂ → ℂ}
  {target : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  {E : StatMech.FrontierA.CompactExhaustion U}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hF : ∀ n, DifferentiableOn ℂ (F n) U)
  (htarget : DifferentiableOn ℂ target U)
  (htarget_ne : target z₀ ≠ 0)
  (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
  (hidentifyDeriv : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ → StrictMono ψ → TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U → Set.EqOn (deriv (fun z => f z ^ 2)) (deriv (fun z => target z ^ 2)) U ∧ f z₀ = target z₀) :
-- imply
  TendstoLocallyUniformlyOn F target atTop U ∧ TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
-- proof
  apply StatMech.Universality.isingFermionic_fullConvergence_of_compactBounds_and_squareDeriv F target U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne E hbounded hidentifyDeriv

/--
[isingFermionic_fullConvergence_of_compactBounds_and_primitiveIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean)
-/
@[path]
private lemma isingFermionic_fullConvergence_of_compactBounds_and_primitiveIm_eq
  {F : ℕ → ℂ → ℂ}
  {target Phi : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  {E : StatMech.FrontierA.CompactExhaustion U}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hF : ∀ n, DifferentiableOn ℂ (F n) U)
  (htarget : DifferentiableOn ℂ target U)
  (htarget_ne : target z₀ ≠ 0)
  (hPhi : DifferentiableOn ℂ Phi U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) U)
  (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
  (hidentifyPrimitive : ∀ (phi psi : ℕ → ℕ) (f : ℂ → ℂ), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun n ↦ F (phi (psi n))) f atTop U → ∃ (P : ℂ → ℂ) (C : ℝ), DifferentiableOn ℂ P U ∧ Set.EqOn (deriv P) (fun z ↦ f z ^ 2) U ∧ (∀ z ∈ U, (P z).im = (Phi z).im + C) ∧ f z₀ = target z₀) :
-- imply
  TendstoLocallyUniformlyOn F target atTop U ∧ TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
-- proof
  apply StatMech.Universality.isingFermionic_fullConvergence_of_compactBounds_and_primitiveIm F target Phi U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne hPhi hPhideriv E hbounded hidentifyPrimitive


-- created on 2026-10-23
