/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/Hurwitz.lean -/

import Theorem.Analysis.Complex.Hurwitz
import Lemma.Complex.Hurwitz
open Filter Set
open scoped Topology

/-!
# Tests for the Hurwitz zero-free limit theorem (N327)
-/


example {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hne : ∀ᶠ n in atTop, ∀ z ∈ U, F n z ≠ 0) :
    Set.EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 :=
  hlim.eqOn_zero_or_ne_zero (Eventually.of_forall hF) hU hconn hne

example {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hne : ∀ᶠ n in atTop, ∀ z ∈ U, F n z ≠ 0)
    (hex : ∃ z ∈ U, f z ≠ 0) :
    ∀ z ∈ U, f z ≠ 0 :=
  hlim.ne_zero_of_exists_ne_zero (Eventually.of_forall hF) hU hconn hne hex

example {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hne : ∀ n, ∀ z ∈ U, F n z ≠ 0) :
    Set.EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 :=
  hlim.eqOn_zero_or_ne_zero (Eventually.of_forall hF) hU hconn
    (Eventually.of_forall hne)

example {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hnonempty : U.Nonempty)
    (hlim : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (_ : ℂ) => ((2 : ℂ)⁻¹) ^ n) 0 atTop U) :
    Set.EqOn (0 : ℂ → ℂ) 0 U := by
  have hF : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun _ : ℂ => ((2 : ℂ)⁻¹) ^ n) U :=
    Eventually.of_forall fun n => differentiableOn_const (((2 : ℂ)⁻¹) ^ n)
  have hne : ∀ᶠ n in atTop, ∀ z ∈ U,
      (fun _ : ℂ => ((2 : ℂ)⁻¹) ^ n) z ≠ 0 :=
    Eventually.of_forall fun n _ _ => pow_ne_zero n (inv_ne_zero two_ne_zero)
  rcases hlim.eqOn_zero_or_ne_zero hF hU hconn hne with hzero | hzeroFree
  · exact hzero
  · obtain ⟨z, hz⟩ := hnonempty
    exact (hzeroFree z hz rfl).elim

example {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) (∅ : Set ℂ))
    (hlim : TendstoLocallyUniformlyOn F f atTop ∅)
    (hne : ∀ᶠ n in atTop, ∀ z ∈ (∅ : Set ℂ), F n z ≠ 0) :
    Set.EqOn f 0 ∅ ∨ ∀ z ∈ (∅ : Set ℂ), f z ≠ 0 :=
  hlim.eqOn_zero_or_ne_zero (Eventually.of_forall hF) isOpen_empty
    isPreconnected_empty hne

