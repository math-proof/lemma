import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.WeightedFibonacciBinet
open MetaMathlibExt


/--
[binet_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/WeightedFibonacciBinet.lean)
-/
@[path]
private lemma binet_general_eq
  {r : ℕ}
  {A c : Fin r → ℝ}
  {a : ℕ → ℝ}
  {p : Polynomial ℝ}
  {lam : ℝ}
-- given
  (hr : 2 ≤ r)
  (hA : ∀ k, 0 ≤ A k)
  (hc : ∀ k, 0 ≤ c k)
  (hAr : ∃ i : Fin r, i.val + 1 = r ∧ 0 < A i)
  (hcpos : ∃ k₀, 0 < c k₀)
  (hgcd : ∀ d : ℕ, (∀ k : Fin r, 0 < A k → d ∣ k.val + 1) → d = 1)
  (ha_init : ∀ n (h : n < r), a n = c ⟨n, h⟩)
  (ha_rec : ∀ n, r ≤ n → a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val)))
  (hp : p = Polynomial.X ^ r - Finset.sum Finset.univ (fun k : Fin r => Polynomial.C (A k) * Polynomial.X ^ (r - 1 - k.val)))
  (hlam_pos : 0 < lam)
  (hlam_root : p.IsRoot lam) :
-- imply
  ∃ C : ℝ, 0 < C ∧
    Asymptotics.IsLittleO Filter.atTop (fun n => a n - C * lam ^ n)
    (fun n => lam ^ n) ∧
    Filter.Tendsto (fun n => a (n + 1) / a n) Filter.atTop (nhds lam) := by
-- proof
  apply MetaMathlibExt.binet_general r hr A c hA hc hAr hcpos hgcd a ha_init ha_rec p hp lam hlam_pos hlam_root

/--
[binet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/WeightedFibonacciBinet.lean)
-/
@[path]
private lemma binet_eq
  {r : ℕ}
  {A c : Fin r → ℝ}
  {a : ℕ → ℝ}
  {p : Polynomial ℝ}
  {lam : ℝ}
-- given
  (hr : 2 ≤ r)
  (hA : ∀ k, 0 ≤ A k)
  (hc : ∀ k, 0 ≤ c k)
  (hAr : ∃ i : Fin r, i.val + 1 = r ∧ 0 < A i)
  (hcpos : ∃ k₀, 0 < c k₀)
  (hgcd : ∀ d : ℕ, (∀ k : Fin r, 0 < A k → d ∣ k.val + 1) → d = 1)
  (ha_init : ∀ n (h : n < r), a n = c ⟨n, h⟩)
  (ha_rec : ∀ n, r ≤ n → a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val)))
  (hp : p = Polynomial.X ^ r - Finset.sum Finset.univ (fun k : Fin r => Polynomial.C (A k) * Polynomial.X ^ (r - 1 - k.val)))
  (hlam_pos : 0 < lam)
  (hlam_root : p.IsRoot lam)
  (hlam_simple : ¬ p.derivative.IsRoot lam)
  (hlam_dom : ∀ z : ℂ, (p.map Complex.ofRealHom).IsRoot z → ‖z‖ ≤ lam ∧ (‖z‖ = lam → z = ↑lam)) :
-- imply
  ∃ C : ℝ, 0 < C ∧
    Asymptotics.IsLittleO Filter.atTop (fun n => a n - C * lam ^ n)
    (fun n => lam ^ n) ∧
    Filter.Tendsto (fun n => a (n + 1) / a n) Filter.atTop (nhds lam) := by
-- proof
  apply MetaMathlibExt.binet r hr A c hA hc hAr hcpos hgcd a ha_init ha_rec p hp lam hlam_pos hlam_root hlam_simple hlam_dom


-- created on 2026-10-20
