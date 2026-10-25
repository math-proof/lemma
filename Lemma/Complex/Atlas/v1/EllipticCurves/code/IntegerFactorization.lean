import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part4
open Nat Real Filter Asymptotics Finset PollardPM1 ECMFactoring MontgomeryTorsion
open Nat Finset


/--
[isSmooth_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma isSmooth_iff
  {B n : ℕ} :
-- imply
  IsSmooth B n ↔ n ≠ 0 ∧ ∀ p ∈ n.primeFactorsList, p ≤ B := by
-- proof
  simp only [IsSmooth, Nat.smoothNumbers, Set.mem_setOf_eq, Nat.lt_add_one_iff]

/--
[mem_factorBase_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma mem_factorBase_iff
  {q B : ℕ} :
-- imply
  q ∈ factorBase B ↔ q ≤ B ∧ q.Prime := by
-- proof
  simp only [factorBase, Nat.mem_primesBelow, Nat.lt_add_one_iff]
section DiscreteLog
variable {G : Type*} [CommGroup G]
  {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
  {n : ℕ} (hn : Nat.card G = n)

/--
[dlog_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dlog_mul
  [CommGroup G]
  {x y : G} :
-- imply
  dlog hg hn (x * y) = dlog hg hn x + dlog hg hn y := by
-- proof
  simp only [dlog, map_mul]; rfl

/--
[dlog_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dlog_inv
  [CommGroup G]
  {x : G} :
-- imply
  dlog hg hn x⁻¹ = -dlog hg hn x := by
-- proof
  simp only [dlog, map_inv]; rfl

/--
[dlog_zpow_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dlog_zpow_g
  [CommGroup G]
  {i : ℤ} :
-- imply
  dlog hg hn (g ^ i) = (i : ZMod n) := by
-- proof
  simp [dlog, zmodMulEquivOfGenerator_symm_apply_zpow]

/--
[dlog_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dlog_zpow
  [CommGroup G]
  {x : G}
  {k : ℤ} :
-- imply
  dlog hg hn (x ^ k) = (k : ZMod n) * dlog hg hn x := by
-- proof
  unfold dlog
  rw [map_zpow]
  show (k : ℤ) • (Multiplicative.toAdd ((zmodMulEquivOfGenerator hg hn).symm x)) = _
  simp [zsmul_eq_mul]

/--
[dlog_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dlog_prod
  [CommGroup G]
  {S : Finset ℕ}
  {f : ℕ → G} :
-- imply
  dlog hg hn (∏ q ∈ S, f q) = ∑ q ∈ S, dlog hg hn (f q) := by
-- proof
  induction S using Finset.induction_on with
  | empty => simp [dlog, map_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, dlog_mul, Finset.sum_insert ha, ih]

/--
[dlog_generator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dlog_generator
  [CommGroup G] :
-- imply
  dlog hg hn g = (1 : ZMod n) := by
-- proof
  have := dlog_zpow_g hg hn (1 : ℤ)
  simp at this
  exact this

/--
[dlog_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dlog_one
  [CommGroup G] :
-- imply
  dlog hg hn (1 : G) = (0 : ZMod n) := by
-- proof
  have := dlog_zpow_g hg hn (0 : ℤ)
  simp at this
  exact this
end DiscreteLog

/--
[index_calculus_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma index_calculus_relation
  [CommGroup G]
  {g : G}
  {n : ℕ}
  {S : Finset ℕ}
  {f : ℕ → G}
  {exps : ℕ → ℤ}
  {b : G}
  {e : ℤ}
-- given
  (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
  (hn : Nat.card G = n)
  (hfact : g ^ e * b⁻¹ = ∏ q ∈ S, f q ^ exps q) :
-- imply
  (∑ q ∈ S, (exps q : ZMod n) * dlog hg hn (f q)) + dlog hg hn b = (e : ZMod n) := by
-- proof
  have h1 : dlog hg hn (g ^ e * b⁻¹) = dlog hg hn (∏ q ∈ S, f q ^ exps q) := by
    rw [hfact]
  rw [dlog_mul, dlog_inv, dlog_zpow_g, dlog_prod] at h1
  simp_rw [dlog_zpow] at h1
  have h2 : (e : ZMod n) = (∑ x ∈ S, ↑(exps x) * dlog hg hn (f x)) + dlog hg hn b := by
    rw [← h1]; ring
  exact h2.symm

namespace PollardPM1

/--
[le_foldl_max_init](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma le_foldl_max_init
  {l : List ℕ}
  {init : ℕ} :
-- imply
  init ≤ l.foldl max init := by
-- proof
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    exact le_trans (le_max_left init x) ih

end PollardPM1

namespace PollardPM1

/--
[le_foldl_max_of_mem_list](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma le_foldl_max_of_mem_list
  {l : List ℕ}
  {x : ℕ}
  {init : ℕ}
-- given
  (hx : x ∈ l) :
-- imply
  x ≤ l.foldl max init := by
-- proof
  induction l generalizing init with
  | nil => simp at hx
  | cons head tail ih =>
    simp only [List.foldl]
    obtain rfl | hx' := List.mem_cons.mp hx
    · exact le_trans (le_max_right init x) le_foldl_max_init
    · exact ih hx' _

end PollardPM1

namespace PollardPM1

/--
[isBSmooth_largestPrimeFactor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma isBSmooth_largestPrimeFactor
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  IsBSmooth (largestPrimeFactor n) n :=
-- proof
  ⟨hn, fun _p hp => le_foldl_max_of_mem_list hp 0⟩

end PollardPM1

namespace PollardPM1

/--
[foldl_max_le_of_init_and_elems](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma foldl_max_le_of_init_and_elems
  {l : List ℕ}
  {init B : ℕ}
-- given
  (hinit : init ≤ B)
  (h : ∀ x ∈ l, x ≤ B) :
-- imply
  l.foldl max init ≤ B := by
-- proof
  induction l generalizing init with
  | nil => simpa [List.foldl]
  | cons a as ih =>
    simp only [List.foldl]
    have ha : a ≤ B := h a List.mem_cons_self
    apply ih (max_le hinit ha)
    intro x hx
    exact h x (List.mem_cons_of_mem a hx)

end PollardPM1

namespace PollardPM1

/--
[factorization_le_clog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma factorization_le_clog
  {q n N : ℕ}
-- given
  (hq : 1 < q)
  (hn : n ≠ 0)
  (hnN : n < N) :
-- imply
  n.factorization q ≤ Nat.clog q N := by
-- proof
  have h1 := Nat.ordProj_dvd n q
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
  exact le_of_lt ((Nat.lt_clog_iff_pow_lt hq).mpr (lt_of_le_of_lt h2 hnN))

end PollardPM1

namespace PollardPM1

/--
[smoothExponent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma smoothExponent_pos
  {N B : ℕ} :
-- imply
  0 < smoothExponent N B := by
-- proof
  unfold smoothExponent
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.Prime.pos (Nat.mem_primesBelow.mp hℓ).2).ne')

end PollardPM1

namespace PollardPM1

/--
[prime_not_dvd_smoothExponent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma prime_not_dvd_smoothExponent
  {q N B : ℕ}
-- given
  (hq : Nat.Prime q)
  (hqB : B < q) :
-- imply
  ¬(q ∣ smoothExponent N B) := by
-- proof
  unfold smoothExponent
  apply hq.prime.not_dvd_finset_prod (g := fun ℓ => ℓ ^ Nat.clog ℓ N)
  intro ℓ hℓ
  rw [Nat.mem_primesBelow] at hℓ
  intro h_dvd
  have hℓq : ℓ ≠ q := by omega
  have hq_dvd_ℓ : q ∣ ℓ := hq.prime.dvd_of_dvd_pow h_dvd
  obtain h | h := hℓ.2.eq_one_or_self_of_dvd q hq_dvd_ℓ
  · exact hq.ne_one h
  · exact hℓq h.symm

end PollardPM1

namespace PollardPM1

/--
[dvd_smoothExponent_of_isBSmooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma dvd_smoothExponent_of_isBSmooth
  {n N B : ℕ}
-- given
  (hsmooth : IsBSmooth B n)
  (hnN : n < N) :
-- imply
  n ∣ smoothExponent N B := by
-- proof
  rw [← Nat.factorization_le_iff_dvd hsmooth.1 (smoothExponent_pos N B).ne']
  rw [Finsupp.le_iff]
  intro q hq_supp
  rw [Nat.support_factorization] at hq_supp
  have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_supp
  have hqB : q ≤ B := by
    rw [Nat.mem_primeFactors_iff_mem_primeFactorsList] at hq_supp
    exact hsmooth.2 q hq_supp
  have h_dvd : q ^ (Nat.clog q N) ∣ smoothExponent N B :=
    Finset.dvd_prod_of_mem _ (by rw [Nat.mem_primesBelow]; exact ⟨by omega, hq_prime⟩)
  have h_fact_ge : Nat.clog q N ≤ (smoothExponent N B).factorization q := by
    have := (Nat.factorization_le_iff_dvd
      (pow_ne_zero _ hq_prime.pos.ne') (smoothExponent_pos N B).ne').mpr h_dvd
    have h := this q
    rwa [hq_prime.factorization_pow, Finsupp.single_apply, if_pos rfl] at h
  exact le_trans (factorization_le_clog hq_prime.one_lt hsmooth.1 hnN) h_fact_ge

end PollardPM1

namespace PollardPM1

/--
[pow_smoothExponent_eq_one_mod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma pow_smoothExponent_eq_one_mod
  {p N B : ℕ}
  {u : (ZMod p)ˣ}
-- given
  (hp : Nat.Prime p)
  (hsmooth : IsBSmooth B (p - 1))
  (hnN : p - 1 < N) :
-- imply
  (u : ZMod p) ^ (smoothExponent N B) = 1 := by
-- proof
  have h_dvd : p.totient ∣ smoothExponent N B := by
    rw [Nat.totient_prime hp]
    exact dvd_smoothExponent_of_isBSmooth hsmooth hnN
  obtain ⟨k, hk⟩ := h_dvd
  rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, one_pow]

end PollardPM1

namespace PollardPM1

/--
[gcd_proper_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma gcd_proper_divisor
  {n N p q : ℕ}
-- given
  (hpN : p ∣ N)
  (hqN : q ∣ N)
  (hp : Nat.Prime p)
  (hpn : p ∣ n)
  (hqn : ¬(q ∣ n))
  (hN : 1 < N) :
-- imply
  1 < Nat.gcd n N ∧ Nat.gcd n N < N := by
-- proof
  constructor
  · have : p ∣ Nat.gcd n N := Nat.dvd_gcd hpn hpN
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right n (by omega)) this)
  · have hgcd_dvd_N : Nat.gcd n N ∣ N := Nat.gcd_dvd_right n N
    have hgcd_dvd_n : Nat.gcd n N ∣ n := Nat.gcd_dvd_left n N
    have hne : Nat.gcd n N ≠ N := by
      intro heq
      rw [heq] at hgcd_dvd_n
      exact hqn (dvd_trans hqN hgcd_dvd_n)
    exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) hgcd_dvd_N) hne

end PollardPM1

namespace PollardPM1

/--
[smoothExponent_dvd_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma smoothExponent_dvd_of_le
  {N B₁ B₂ : ℕ}
-- given
  (h : B₁ ≤ B₂) :
-- imply
  smoothExponent N B₁ ∣ smoothExponent N B₂ := by
-- proof
  unfold smoothExponent
  apply Finset.prod_dvd_prod_of_subset
  intro ℓ hℓ
  rw [Nat.mem_primesBelow] at hℓ ⊢
  exact ⟨by omega, hℓ.2⟩

end PollardPM1

namespace PollardPM1

/--
[list_foldl_max_mem_or_eq_init](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma list_foldl_max_mem_or_eq_init
-- imply
  ∀ (l : List ℕ) (init : ℕ), l.foldl max init ∈ l ∨ l.foldl max init = init := by
-- proof
  intro l
  induction l with
  | nil => intro init; right; rfl
  | cons a as ih =>
    intro init
    simp only [List.foldl]
    obtain h | h := ih (max init a)
    · left; exact List.mem_cons_of_mem a h
    · rw [h]
      by_cases hle : init ≤ a
      · left; simp only [max_eq_right hle]; exact List.Mem.head as
      · right; omega

end PollardPM1

namespace PollardPM1

/--
[largestPrimeFactor_mem_primeFactorsList](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma largestPrimeFactor_mem_primeFactorsList
  {n : ℕ}
-- given
  (h : Nat.Prime (largestPrimeFactor n)) :
-- imply
  largestPrimeFactor n ∈ n.primeFactorsList := by
-- proof
  unfold largestPrimeFactor at h ⊢
  obtain hm | hm := list_foldl_max_mem_or_eq_init n.primeFactorsList 0
  · exact hm
  · rw [hm] at h; exact absurd h (by decide)

end PollardPM1

namespace PollardPM1

/--
[largestPrimeFactor_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma largestPrimeFactor_dvd
  {n : ℕ}
-- given
  (h : Nat.Prime (largestPrimeFactor n))
  (hn : n ≠ 0) :
-- imply
  largestPrimeFactor n ∣ n :=
-- proof
  ((Nat.mem_primeFactorsList hn).mp (largestPrimeFactor_mem_primeFactorsList h)).2

end PollardPM1

namespace PollardPM1

/--
[card_mth_roots_mul_largest_prime_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma card_mth_roots_mul_largest_prime_le
  {q m : ℕ}
-- given
  (hq : Nat.Prime q)
  (hℓq_prime : Nat.Prime (largestPrimeFactor (q - 1)))
  (hℓq_not_dvd : ¬(largestPrimeFactor (q - 1) ∣ m)) :
-- imply
  Nat.card ↥(powMonoidHom (α := (ZMod q)ˣ) m).ker * largestPrimeFactor (q - 1) ≤ q - 1 := by
-- proof
  haveI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq
  rw [IsCyclic.card_powMonoidHom_ker]
  have hqm1_ne : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq.one_lt
  rw [show Nat.card (ZMod q)ˣ = q - 1 from by
    haveI : Fact q.Prime := ⟨hq⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]]
  have h_gcd_dvd : (q - 1).gcd m ∣ q - 1 := Nat.gcd_dvd_left _ _
  have h_not_dvd_gcd : ¬(largestPrimeFactor (q - 1) ∣ (q - 1).gcd m) :=
    fun h => hℓq_not_dvd (dvd_trans h (Nat.gcd_dvd_right _ _))
  have hcop : Nat.Coprime ((q - 1).gcd m) (largestPrimeFactor (q - 1)) := by
    rwa [Nat.coprime_comm, hℓq_prime.coprime_iff_not_dvd]
  have hℓ_dvd : largestPrimeFactor (q - 1) ∣ q - 1 :=
    largestPrimeFactor_dvd hℓq_prime hqm1_ne
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hqm1_ne)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h_gcd_dvd hℓ_dvd)

end PollardPM1

namespace PollardPM1

/--
[largestPrimeFactor_prime_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma largestPrimeFactor_prime_of_pos
  {n : ℕ}
-- given
  (h : 0 < largestPrimeFactor n) :
-- imply
  Nat.Prime (largestPrimeFactor n) := by
-- proof
  unfold largestPrimeFactor at h ⊢
  obtain hm | hm := list_foldl_max_mem_or_eq_init n.primeFactorsList 0
  · exact Nat.prime_of_mem_primeFactorsList hm
  · omega
end PollardPM1
namespace ECMFactoring
open Nat Finset


namespace ECMFactoring

/--
[shortWeierstrass_Δ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
`-16 (4 a³ + 27 b²) = -16 · ecmDiscriminant a b`. -/
lemma shortWeierstrass_Δ {R : Type*} [CommRing R] (a b : R) :
  (shortWeierstrass a b).Δ = -16 * ecmDiscriminant a b := by
  simp only [shortWeierstrass, ecmDiscriminant, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

end ECMFactoring

namespace ECMFactoring

/--
[ECMCurveParams.point_on_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ECMCurveParams.point_on_curve
  {params : ECMCurveParams} :
-- imply
  WeierstrassCurve.Affine.Equation params.curve params.x₀ params.y₀ := by
-- proof
  unfold WeierstrassCurve.Affine.Equation Polynomial.evalEval
  simp only [ECMCurveParams.curve, shortWeierstrass, ECMCurveParams.b,
    WeierstrassCurve.Affine.polynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  ring

end ECMFactoring

namespace ECMFactoring

/--
[ecmSmoothExponent_bound_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ecmSmoothExponent_bound_le
  {ℓ M : ℕ}
-- given
  (_hℓ : 1 < ℓ) :
-- imply
  ℓ ^ (ecmSmoothExponent ℓ M - 1) ≤ (Nat.sqrt M + 1) ^ 2 := by
-- proof
  simp only [ecmSmoothExponent, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self ℓ (by positivity)

end ECMFactoring

namespace ECMFactoring

/--
[ecmSmoothExponent_bound_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ecmSmoothExponent_bound_lt
  {ℓ M : ℕ}
-- given
  (hℓ : 1 < ℓ) :
-- imply
  (Nat.sqrt M + 1) ^ 2 < ℓ ^ ecmSmoothExponent ℓ M := by
-- proof
  simp only [ecmSmoothExponent]
  exact Nat.lt_pow_succ_log_self hℓ _

end ECMFactoring

namespace ECMFactoring

/--
[ecmSmoothScalar_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ecmSmoothScalar_pos
  {B M : ℕ} :
-- imply
  0 < ecmSmoothScalar B M := by
-- proof
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

end ECMFactoring

namespace ECMFactoring

/--
[ecmSmoothScalar_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ecmSmoothScalar_smooth
  {B M : ℕ} :
-- imply
  ecmSmoothScalar B M ∈ Nat.smoothNumbers B := by
-- proof
  rw [Nat.mem_smoothNumbers]
  constructor
  · exact (ecmSmoothScalar_pos B M).ne'
  · intro q hq
    rw [Nat.mem_primeFactorsList (ecmSmoothScalar_pos B M).ne'] at hq
    obtain ⟨hqp, hq_dvd⟩ := hq
    simp only [ecmSmoothScalar] at hq_dvd
    rw [hqp.prime.dvd_finset_prod_iff (fun ℓ => ℓ ^ ecmSmoothExponent ℓ M)] at hq_dvd
    obtain ⟨ℓ, hℓ_mem, hq_dvd_pow⟩ := hq_dvd
    rw [Finset.mem_filter, Finset.mem_range] at hℓ_mem
    have hq_dvd_ℓ := hqp.dvd_of_dvd_pow hq_dvd_pow
    have hqℓ := (Nat.prime_dvd_prime_iff_eq hqp hℓ_mem.2).mp hq_dvd_ℓ
    omega

end ECMFactoring

namespace ECMFactoring

/--
[factorization_le_log_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma factorization_le_log_of_pos
  {n p : ℕ}
-- given
  (hn : 0 < n)
  (hp : 1 < p) :
-- imply
  n.factorization p ≤ Nat.log p n :=
-- proof
  Nat.le_log_of_pow_le hp (le_of_dvd hn (Nat.ordProj_dvd n p))

end ECMFactoring

namespace ECMFactoring

/--
[prime_pow_dvd_ecmSmoothScalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma prime_pow_dvd_ecmSmoothScalar
  {B M p : ℕ}
-- given
  (hp : Nat.Prime p)
  (hpB : p < B) :
-- imply
  p ^ ecmSmoothExponent p M ∣ ecmSmoothScalar B M :=
-- proof
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpB, hp⟩)

end ECMFactoring

namespace ECMFactoring

/--
[smooth_dvd_ecmSmoothScalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma smooth_dvd_ecmSmoothScalar
  {n B M : ℕ}
-- given
  (hn : n ≠ 0)
  (hsmooth : n ∈ Nat.smoothNumbers B)
  (hbound : n ≤ (Nat.sqrt M + 1) ^ 2) :
-- imply
  n ∣ ecmSmoothScalar B M := by
-- proof
  rw [Nat.mem_smoothNumbers] at hsmooth
  rw [← Nat.factorization_le_iff_dvd hn (ecmSmoothScalar_pos B M).ne']
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hfp : n.factorization p = 0
    · simp [hfp]
    · have hpn : p ∈ n.primeFactorsList := by
      rw [Nat.mem_primeFactorsList hn]
      exact ⟨hp, (hp.dvd_iff_one_le_factorization hn).mpr (Nat.pos_of_ne_zero hfp)⟩
      have hpB : p < B := hsmooth.2 p hpn
      have hdvd := prime_pow_dvd_ecmSmoothScalar (M := M) hp hpB
      have hfact := (hp.pow_dvd_iff_le_factorization (ecmSmoothScalar_pos B M).ne').mp hdvd
      calc n.factorization p
        ≤ Nat.log p n :=
          factorization_le_log_of_pos (Nat.pos_of_ne_zero hn) hp.one_lt
        _ ≤ Nat.log p ((Nat.sqrt M + 1) ^ 2) := Nat.log_mono_right hbound
        _ ≤ (ecmSmoothScalar B M).factorization p := by
          simp only [ecmSmoothExponent] at hfact; omega
  · simp [hp]

end ECMFactoring

namespace ECMFactoring

/--
[ecm_algebraic_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ecm_algebraic_step
  {cfg : ECMConfig}
  {params : ECMCurveParams}
  {p₁ p₂ : ℕ}
  [Fact (Nat.Prime p₁)]
  [Fact (Nat.Prime p₂)]
  {P₁ : (params.curveModP p₁).Point}
  {P₂ : (params.curveModP p₂).Point}
-- given
  (hp₁M : p₁ ≤ cfg.M)
  (hsmooth₁ : addOrderOf P₁ ∈ Nat.smoothNumbers cfg.B)
  (hord₁_bound : addOrderOf P₁ ≤ (Nat.sqrt p₁ + 1) ^ 2)
  (hnotsmooth₂ : addOrderOf P₂ ∉ Nat.smoothNumbers cfg.B) :
-- imply
  (ecmSmoothScalar cfg.B cfg.M) • P₁ = 0 ∧ (ecmSmoothScalar cfg.B cfg.M) • P₂ ≠ 0 := by
-- proof
  constructor
  ·
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    have hord₁_pos : addOrderOf P₁ ≠ 0 :=
      (Nat.mem_smoothNumbers.mp hsmooth₁).1
    apply smooth_dvd_ecmSmoothScalar hord₁_pos hsmooth₁
    calc addOrderOf P₁
      ≤ (Nat.sqrt p₁ + 1) ^ 2 := hord₁_bound
      _ ≤ (Nat.sqrt cfg.M + 1) ^ 2 := by
        apply Nat.pow_le_pow_left
        exact Nat.add_le_add_right (Nat.sqrt_le_sqrt hp₁M) 1
  ·
    intro h
    apply hnotsmooth₂
    exact Nat.mem_smoothNumbers_of_dvd (ecmSmoothScalar_smooth cfg.B cfg.M)
      (addOrderOf_dvd_of_nsmul_eq_zero h)
end ECMFactoring
namespace MontgomeryTorsion
open Nat Finset

end ECMFactoring

namespace MontgomeryTorsion

/--
[ne_add_two_zero_of_sq_ne_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ne_add_two_zero_of_sq_ne_four
  [Field k]
  {A : k}
-- given
  (h : A ^ 2 ≠ 4) :
-- imply
  A + 2 ≠ 0 := by
-- proof
  intro h_eq
  exact h (sub_eq_zero.mp (by have : A ^ 2 - 4 = (A + 2) * (A - 2) := by ring
    rw [this, h_eq, zero_mul]))

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[ne_sub_two_zero_of_sq_ne_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma ne_sub_two_zero_of_sq_ne_four
  [Field k]
  {A : k}
-- given
  (h : A ^ 2 ≠ 4) :
-- imply
  A - 2 ≠ 0 := by
-- proof
  intro h_eq
  exact h (sub_eq_zero.mp (by have : A ^ 2 - 4 = (A + 2) * (A - 2) := by ring
    rw [this, h_eq, mul_zero]))

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[not_isSquare_disc_of_no_roots](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma not_isSquare_disc_of_no_roots
  [Field k]
  {A : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (hno_root : ∀ r : k, r ^ 2 + A * r + 1 ≠ 0) :
-- imply
  ¬ IsSquare (A ^ 2 - 4) := by
-- proof
  intro ⟨d, hd⟩
  have hd' : d ^ 2 = A ^ 2 - 4 := by rw [sq]; linear_combination -hd
  have h4 : (4 : k) ≠ 0 := by
    intro h; apply h2; have : (4 : k) = 2 * 2 := by ring
    rw [this] at h; exact (mul_eq_zero.mp h).elim id id
  have : ((-A + d) / 2) ^ 2 + A * ((-A + d) / 2) + 1 = 0 := by
    suffices h : 4 * (((-A + d) / 2) ^ 2 + A * ((-A + d) / 2) + 1) = 0 by
      exact (mul_eq_zero.mp h).resolve_left h4
    have key : 4 * (((-A + d) / 2) ^ 2 + A * ((-A + d) / 2) + 1) =
      d ^ 2 - A ^ 2 + 4 := by field_simp; ring
    rw [key]; linear_combination hd'
  exact hno_root _ this

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[isSquare_mul_or_of_not_isSquare_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma isSquare_mul_or_of_not_isSquare_mul
  [Field k]
  [Fintype k]
  [DecidableEq k]
  {a b c : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h : ¬ IsSquare (a * b)) :
-- imply
  IsSquare (a * c) ∨ IsSquare (b * c) := by
-- proof
  have hχ_ab := quadraticChar_neg_one_iff_not_isSquare.mpr h
  rw [map_mul] at hχ_ab
  have hχa := quadraticChar_dichotomy (a := a) ha
  have hχb := quadraticChar_dichotomy (a := b) hb
  have hχc := quadraticChar_dichotomy (a := c) hc
  obtain ha1 | ha1 <;> rcases hχb with hb1 | hb1 <;> := hχa
    rw [ha1, hb1] at hχ_ab <;> simp at hχ_ab
  · rcases hχc with hc1 | hc1
    · left; exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hc)).mp
      (by rw [map_mul, ha1, hc1, mul_one])
    · right; exact (quadraticChar_one_iff_isSquare (mul_ne_zero hb hc)).mp
      (by rw [map_mul, hb1, hc1]; ring)
  · rcases hχc with hc1 | hc1
    · right; exact (quadraticChar_one_iff_isSquare (mul_ne_zero hb hc)).mp
      (by rw [map_mul, hb1, hc1, mul_one])
    · left; exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hc)).mp
      (by rw [map_mul, ha1, hc1]; ring)

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[exists_By_sq_eq_of_isSquare_mul_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma exists_By_sq_eq_of_isSquare_mul_inv
  [Field k]
  {A B : k}
-- given
  (hB : B ≠ 0)
  (h : IsSquare (A * B⁻¹)) :
-- imply
  ∃ y : k, B * y ^ 2 = A := by
-- proof
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  have h1 : A = t * t * B := by
    calc A = A * B⁻¹ * B := by field_simp
    _ = t * t * B := by rw [ht]
  rwa [sq, mul_comm B (t * t)]

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[montgomery_torsion_10_14](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma montgomery_torsion_10_14
  [Field k]
  [Fintype k]
  [DecidableEq k]
  {A B : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (hB : B ≠ 0)
  (hA : A ^ 2 ≠ 4) :
-- imply
  (∃ r s : k, r ≠ 0 ∧ s ≠ 0 ∧ r ≠ s ∧ r ^ 2 + A * r + 1 = 0 ∧ s ^ 2 + A * s + 1 = 0) ∨ (∃ y : k, B * y ^ 2 = A + 2) ∨ (∃ y : k, B * y ^ 2 = A - 2) := by
-- proof
  by_cases h : ∃ r : k, r ^ 2 + A * r + 1 = 0
  ·
    left
    obtain ⟨r, hr⟩ := h
    refine ⟨r, -A - r, ?_, ?_, ?_, hr, ?_⟩
    ·
      intro heq; rw [heq] at hr; simp at hr
    ·
      intro heq
      have : (-A - r) ^ 2 + A * (-A - r) + 1 = 0 := by linear_combination hr
      rw [heq] at this; simp at this
    ·
      intro heq
      apply hA
      have h2r : 2 * r = -A := by linear_combination heq
      have hA_eq : A = -(2 * r) := by linear_combination h2r
      have hr1 : r ^ 2 = 1 := by
        have := hr; rw [hA_eq] at this; linear_combination -this
      calc A ^ 2 = (-(2 * r)) ^ 2 := by rw [hA_eq]
        _ = 4 * r ^ 2 := by ring
        _ = 4 * 1 := by rw [hr1]
        _ = 4 := by ring
    ·
      linear_combination hr
  ·
    right
    push Not at h
    have hdisc : ¬ IsSquare (A ^ 2 - 4) := not_isSquare_disc_of_no_roots h2 h
    have hfactor : A ^ 2 - 4 = (A + 2) * (A - 2) := by ring
    rw [hfactor] at hdisc
    have hAp2 : A + 2 ≠ 0 := ne_add_two_zero_of_sq_ne_four hA
    have hAm2 : A - 2 ≠ 0 := ne_sub_two_zero_of_sq_ne_four hA
    have hBinv : B⁻¹ ≠ 0 := inv_ne_zero hB
    obtain hsq | hsq := isSquare_mul_or_of_not_isSquare_mul hAp2 hAm2 hBinv hdisc
    · left; exact exists_By_sq_eq_of_isSquare_mul_inv hB hsq
    · right; exact exists_By_sq_eq_of_isSquare_mul_inv hB hsq

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[isOrder2Point_of_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma isOrder2Point_of_root
  [Field k]
  {A B r : k}
-- given
  (hr : r ^ 2 + A * r + 1 = 0)
  (hr0 : r ≠ 0) :
-- imply
  IsOrder2Point A B r := by
-- proof
  refine ⟨?_, hr0⟩
  unfold MontgomeryOnCurve
  have : r ^ 3 + A * r ^ 2 + r = r * (r ^ 2 + A * r + 1) := by ring
  rw [this, hr, mul_zero]; ring

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[isOrder4Point_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma isOrder4Point_at_one
  [Field k]
  {A B y : k}
-- given
  (hy : B * y ^ 2 = A + 2)
  (hyNe : y ≠ 0) :
-- imply
  IsOrder4Point A B 1 y :=
-- proof
  ⟨by unfold MontgomeryOnCurve; linear_combination hy, hyNe, Or.inl rfl⟩

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[isOrder4Point_at_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma isOrder4Point_at_neg_one
  [Field k]
  {A B y : k}
-- given
  (hy : B * y ^ 2 = A - 2)
  (hyNe : y ≠ 0) :
-- imply
  IsOrder4Point A B (-1) y :=
-- proof
  ⟨by unfold MontgomeryOnCurve; linear_combination hy, hyNe, Or.inr rfl⟩

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[y_ne_zero_of_By_sq_eq_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma y_ne_zero_of_By_sq_eq_add_two
  [Field k]
  {A B y : k}
-- given
  (hA : A ^ 2 ≠ 4)
  (hy : B * y ^ 2 = A + 2) :
-- imply
  y ≠ 0 := by
-- proof
  intro heq; rw [heq, sq, mul_zero, mul_zero] at hy; apply hA
  have : A = -(2 : k) := by linear_combination hy.symm
  rw [this]; ring

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[y_ne_zero_of_By_sq_eq_sub_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma y_ne_zero_of_By_sq_eq_sub_two
  [Field k]
  {A B y : k}
-- given
  (hA : A ^ 2 ≠ 4)
  (hy : B * y ^ 2 = A - 2) :
-- imply
  y ≠ 0 := by
-- proof
  intro heq; rw [heq, sq, mul_zero, mul_zero] at hy; apply hA
  have : A = (2 : k) := by linear_combination hy.symm
  rw [this]; ring

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[theorem_10_15_squareness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma theorem_10_15_squareness
  [Field k]
  {a b x₀ u v : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (hcurve_P : ShortWeierstrassOnCurve a b u v)
  (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
  (hv : v ≠ 0)
  (hdouble : x₀ = ((3 * u ^ 2 + a) / (2 * v)) ^ 2 - 2 * u) :
-- imply
  (u - x₀) ^ 2 = 3 * x₀ ^ 2 + a ∧ (3 * x₀ ^ 2 + a ≠ 0) := by
-- proof
  have hb : b = -x₀ ^ 3 - a * x₀ := by
    unfold ShortWeierstrassOnCurve at hcurve_2P; simp at hcurve_2P
    linear_combination -hcurve_2P
  have hv2 : v ^ 2 = u ^ 3 + a * u + (-x₀ ^ 3 - a * x₀) := by
    rw [hb] at hcurve_P; exact hcurve_P
  have h2v : (2 * v) ≠ 0 := mul_ne_zero h2 hv
  have hdbl_clear : (x₀ + 2 * u) * ((2 * v) ^ 2) = (3 * u ^ 2 + a) ^ 2 := by
    have h1 : x₀ + 2 * u = ((3 * u ^ 2 + a) / (2 * v)) ^ 2 := by
      linear_combination hdouble
    rw [h1, div_pow, div_mul_cancel₀]
    exact pow_ne_zero 2 h2v
  have h_denom : 4 * (x₀ + 2 * u) * (u ^ 3 + a * u - x₀ ^ 3 - a * x₀) =
    (3 * u ^ 2 + a) ^ 2 := by
    calc 4 * (x₀ + 2 * u) * (u ^ 3 + a * u - x₀ ^ 3 - a * x₀)
      = (x₀ + 2 * u) * (4 * (u ^ 3 + a * u - x₀ ^ 3 - a * x₀)) := by ring
      _ = (x₀ + 2 * u) * (4 * v ^ 2) := by rw [hv2]; ring
      _ = (x₀ + 2 * u) * ((2 * v) ^ 2) := by ring
      _ = (3 * u ^ 2 + a) ^ 2 := hdbl_clear
  have hsq_eq : ((u - x₀) ^ 2 - (3 * x₀ ^ 2 + a)) ^ 2 = 0 := by
    linear_combination -h_denom
  have huz : (u - x₀) ^ 2 = 3 * x₀ ^ 2 + a := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq_eq
    linear_combination this
  exact ⟨huz, by
    intro h0
    have hu_eq : u = x₀ := by
      rw [h0] at huz
      exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp huz)
    have : v ^ 2 = 0 := by rw [hu_eq] at hv2; linear_combination hv2
    exact hv (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)⟩

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[theorem_10_15_isomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma theorem_10_15_isomorphism
  [Field k]
  {a b x₀ A B : k}
-- given
  (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
  (hB_sq : B ^ 2 * (3 * x₀ ^ 2 + a) = 1)
  (hA : A = 3 * x₀ * B) :
-- imply
  ∀ x y : k, ShortWeierstrassOnCurve a b x y → MontgomeryOnCurve A B (B * (x - x₀)) (B * y) := by
-- proof
  intro x y hxy
  unfold MontgomeryOnCurve
  rw [hA]
  have hb : b = -x₀ ^ 3 - a * x₀ := by
    unfold ShortWeierstrassOnCurve at hcurve_2P; simp at hcurve_2P
    linear_combination -hcurve_2P
  unfold ShortWeierstrassOnCurve at hxy
  rw [hb] at hxy
  have hstep : B ^ 2 * y ^ 2 =
    B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (x - x₀) := by
    have hpoly : x ^ 3 + a * x + (-x₀ ^ 3 - a * x₀) =
      (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (3 * x₀ ^ 2 + a) * (x - x₀) := by ring
    calc B ^ 2 * y ^ 2
      = B ^ 2 * (x ^ 3 + a * x + (-x₀ ^ 3 - a * x₀)) := by rw [hxy]
      _ = B ^ 2 * ((x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) +
        (3 * x₀ ^ 2 + a) * (x - x₀)) := by rw [hpoly]
      _ = B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) +
        B ^ 2 * ((3 * x₀ ^ 2 + a) * (x - x₀)) := by ring
      _ = B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (x - x₀) := by
        congr 1
        rw [show B ^ 2 * ((3 * x₀ ^ 2 + a) * (x - x₀)) =
          B ^ 2 * (3 * x₀ ^ 2 + a) * (x - x₀) from by ring]
        rw [hB_sq, one_mul]
  calc B * (B * y) ^ 2
    = B * (B ^ 2 * y ^ 2) := by ring
    _ = B * (B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (x - x₀)) := by rw [hstep]
    _ = (B * (x - x₀)) ^ 3 + 3 * x₀ * B * (B * (x - x₀)) ^ 2 + B * (x - x₀) := by ring

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[theorem_10_15_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma theorem_10_15_inverse
  [Field k]
  {a b x₀ A B : k}
-- given
  (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
  (hB_sq : B ^ 2 * (3 * x₀ ^ 2 + a) = 1)
  (hA : A = 3 * x₀ * B) :
-- imply
  ∀ X Y : k, MontgomeryOnCurve A B X Y → ShortWeierstrassOnCurve a b (X / B + x₀) (Y / B) := by
-- proof
  have hB : B ≠ 0 := by intro hB0; rw [hB0] at hB_sq; simp at hB_sq
  have hb : b = -x₀ ^ 3 - a * x₀ := by
    unfold ShortWeierstrassOnCurve at hcurve_2P; simp at hcurve_2P
    linear_combination -hcurve_2P
  intro X Y hXY
  unfold MontgomeryOnCurve at hXY
  unfold ShortWeierstrassOnCurve
  rw [hb, hA] at *
  field_simp
  linear_combination hXY - X * hB_sq

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[theorem_10_15_round_trip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma theorem_10_15_round_trip
  [Field k]
  {x₀ B : k}
-- given
  (hB : B ≠ 0) :
-- imply
  (∀ x y : k, (B * (x - x₀)) / B + x₀ = x ∧ (B * y) / B = y) ∧ (∀ X Y : k, B * ((X / B + x₀) - x₀) = X ∧ B * (Y / B) = Y) :=
-- proof
  ⟨fun x y => ⟨by field_simp; ring, by field_simp⟩,
    fun X Y => ⟨by field_simp; ring, by field_simp⟩⟩

end MontgomeryTorsion

namespace MontgomeryTorsion

/--
[theorem_10_15](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
lemma theorem_10_15
  [Field k]
  {a b x₀ u v : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (hcurve_P : ShortWeierstrassOnCurve a b u v)
  (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
  (hv : v ≠ 0)
  (hdouble : x₀ = ((3 * u ^ 2 + a) / (2 * v)) ^ 2 - 2 * u) :
-- imply
  ((u - x₀) ^ 2 = 3 * x₀ ^ 2 + a ∧ (3 * x₀ ^ 2 + a ≠ 0)) ∧ (∀ B A : k, B ^ 2 * (3 * x₀ ^ 2 + a) = 1 → A = 3 * x₀ * B → (∀ x y : k, ShortWeierstrassOnCurve a b x y → MontgomeryOnCurve A B (B * (x - x₀)) (B * y)) ∧ (∀ X Y : k, MontgomeryOnCurve A B X Y → ShortWeierstrassOnCurve a b (X / B + x₀) (Y / B)) ∧ (∀ x y : k, (B * (x - x₀)) / B + x₀ = x ∧ (B * y) / B = y) ∧ (∀ X Y : k, B * ((X / B + x₀) - x₀) = X ∧ B * (Y / B) = Y)) := by
-- proof
  refine ⟨theorem_10_15_squareness h2 hcurve_P hcurve_2P hv hdouble,
    fun _B _A hB hA => ?_⟩
  have hBne : _B ≠ 0 := by intro h0; rw [h0] at hB; simp at hB
  exact ⟨theorem_10_15_isomorphism hcurve_2P hB hA,
    theorem_10_15_inverse hcurve_2P hB hA,
    (theorem_10_15_round_trip hBne).1,
    (theorem_10_15_round_trip hBne).2⟩

end MontgomeryTorsion

/--
[shortWeierstrass_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean)
-/
@[path]
private lemma shortWeierstrass__eq
  [CommRing R]
  {a b : R} :
-- imply
  (shortWeierstrass a b).Δ = -16 * ecmDiscriminant a b := by
-- proof
  apply ECMFactoring.shortWeierstrass_ a b


-- created on 2026-10-23
