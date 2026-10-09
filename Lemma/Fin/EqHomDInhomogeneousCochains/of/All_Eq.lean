import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_inhomogeneousCochains_d_comp_res_apply](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_inhomogeneousCochains_d_comp_res_apply.lean)
-/

private lemma  PlumbD.neg_one_pow_smul_eq_zsmul {k M : Type} [Ring k] [AddCommGroup M] [Module k M] (m : ℕ) (a : M) :
    (-1 : k) ^ m • a = ((-1 : ℤ) ^ m) • a := by
  rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]
@[path]
private lemma main
  {k G H : Type} [CommRing k] [Group G] [Group H]
  {A : Rep.{0} k G}
  {B : Rep.{0} k H}
  {f : H →* G}
  {T : A →+ B}
  {n : ℕ}
  {x : (Fin n → G) → A}
-- given
  (hT : ∀ (h : H) (a : A), T (A.ρ (f h) a) = B.ρ h (T a)) :
-- imply
  ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => T (x (f ∘ g))) =
      fun g => T (((inhomogeneousCochains A).d n (n + 1)).hom x (f ∘ g)) := by
-- proof
  ext g
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def, inhomogeneousCochains.d_hom_apply,
    inhomogeneousCochains.d_hom_apply, map_add, map_sum]
  have h0 : T ((A.ρ ((⇑f ∘ g) 0)) (x fun i => (⇑f ∘ g) i.succ)) =
      B.ρ (g 0) (T (x (⇑f ∘ fun i => g i.succ))) := hT (g 0) _
  rw [h0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PlumbD.neg_one_pow_smul_eq_zsmul (k := k) (M := B), PlumbD.neg_one_pow_smul_eq_zsmul (k := k) (M := A),
    map_zsmul, Fin.comp_contractNth (· * ·) (· * ·) (fun a b => map_mul f a b)]


-- created on 2026-10-05
