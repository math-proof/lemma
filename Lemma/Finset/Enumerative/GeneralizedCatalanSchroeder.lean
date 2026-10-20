import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
open scoped BigOperators
open MetaMathlibExt


/--
[generalizedCatalanSchroeder_recurrence_functionalEquation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedCatalanSchroeder.lean)
-/
@[path]
private lemma generalizedCatalanSchroeder_recurrence_functionalEquation_eq
  [CommRing R]
  {s t p : R}
  {a : ℕ → R}
-- given
  (ha0 : a 0 = 1)
  (ha1 : a 1 = p)
  (hrec : ∀ n : ℕ, 2 ≤ n → a n = s * a (n - 1) + t * Finset.sum (Finset.range (n - 2)) (fun k => a (k + 1) * a (n - k - 2))) :
-- imply
  PowerSeries.mk a - 1 =
    PowerSeries.C p * PowerSeries.X +
    PowerSeries.C s * PowerSeries.X * (PowerSeries.mk a - 1) +
    PowerSeries.C t * PowerSeries.X * (PowerSeries.mk a - 1) ^ 2 := by
-- proof
  apply MetaMathlibExt.generalizedCatalanSchroeder_recurrence_functionalEquation R s t p a ha0 ha1 hrec

/--
[generalizedCatalanSchroeder_generatingFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedCatalanSchroeder.lean)
-/
@[path]
private lemma generalizedCatalanSchroeder_generatingFunction_eq
  [CommRing R]
  {s t p : R}
  {a : ℕ → R}
  {g f : PowerSeries R}
-- given
  (ha0 : a 0 = 1)
  (ha1 : a 1 = p)
  (hrec : ∀ n : ℕ, 2 ≤ n → a n = s * a (n - 1) + t * Finset.sum (Finset.range (n - 2)) (fun k => a (k + 1) * a (n - k - 2)))
  (hg : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) * g = 1 + PowerSeries.C (p - s + t) * PowerSeries.X)
  (hf : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) ^ 2 * f = PowerSeries.C t * PowerSeries.X * (1 + PowerSeries.C (p - s + t) * PowerSeries.X)) :
-- imply
  PowerSeries.mk a = g * PowerSeries.subst f (PowerSeries.mk (fun n => (catalan n : R))) := by
-- proof
  apply MetaMathlibExt.generalizedCatalanSchroeder_generatingFunction R s t p a ha0 ha1 hrec g hg f hf


-- created on 2026-10-20
