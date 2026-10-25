import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part3
open WeierstrassCurve Classical PadicFiltration
open Classical


/--
[eq_zero_of_isOfFinAddOrder_of_torsionFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma eq_zero_of_isOfFinAddOrder_of_torsionFree
  [AddCommGroup G]
  [IsAddTorsionFree G]
  {g : G}
-- given
  (h : IsOfFinAddOrder g) :
-- imply
  g = 0 := by
-- proof
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at h
  obtain ⟨n, hn, hng⟩ := h
  exact (IsAddTorsionFree.nsmul_right_injective hn.ne') (hng.trans (smul_zero n).symm)

/--
[curve_equation_short_weierstrass](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma curve_equation_short_weierstrass
  {W : WeierstrassCurve ℚ}
  {x₀ y₀ : ℚ}
-- given
  (hW1 : W.a₁ = 0)
  (hW2 : W.a₂ = 0)
  (hW3 : W.a₃ = 0)
  (hns : W.toAffine.Nonsingular x₀ y₀) :
-- imply
  y₀ ^ 2 = x₀ ^ 3 + W.a₄ * x₀ + W.a₆ := by
-- proof
  have heq := hns.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [WeierstrassCurve.toAffine] at heq
  simp only [hW1, hW2, hW3, zero_mul] at heq
  linarith

/--
[rat_is_int_of_nonneg_padic_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma rat_is_int_of_nonneg_padic_val
  {q : ℚ}
-- given
  (h : ∀ p : ℕ, Nat.Prime p → padicValRat p q ≥ 0) :
-- imply
  ∃ z : ℤ, (z : ℚ) = q := by
-- proof
  suffices hd : q.den = 1 by
    exact ⟨q.num, by rw [← Rat.num_divInt_den q, hd]; simp⟩
  by_contra hne
  have hd_pos := q.den_pos
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : q.den ≠ 1)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hge := h p hp
  simp only [padicValRat] at hge
  have hpd : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd (by omega) hpdiv
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hpn : ¬ (p ∣ q.num.natAbs) := by
    intro hpa
    have h1 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpa hpdiv
    rw [hcop] at h1
    have : p ≤ 1 := Nat.le_of_dvd Nat.one_pos h1
    exact absurd this (Nat.not_le.mpr hp.one_lt)
  have hpn0 : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hpn
  simp only [padicValInt, hpn0] at hge
  omega

/--
[rat_sq_int_imp_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma rat_sq_int_imp_int
  {q : ℚ}
-- given
  (h : ∃ z : ℤ, (z : ℚ) = q ^ 2) :
-- imply
  ∃ z : ℤ, (z : ℚ) = q := by
-- proof
  obtain ⟨z, hz⟩ := h
  suffices hd : q.den = 1 by
    exact ⟨q.num, by rw [← Rat.num_divInt_den q, hd]; simp⟩
  have hq2_den : (q * q).den = 1 := by
    have : q * q = q ^ 2 := by ring
    rw [this, ← hz]; exact Rat.den_intCast z
  have hmul := Rat.mul_den q q
  rw [hq2_den] at hmul
  rw [show q.num * q.num = (q.num : ℤ) ^ 2 from by ring] at hmul
  rw [show q.den * q.den = q.den ^ 2 from by ring] at hmul
  rw [Int.natAbs_pow] at hmul
  rw [q.reduced.pow 2 2] at hmul
  simp at hmul
  nlinarith [sq_nonneg q.den]
/-- If a torsion point on a short Weierstrass curve over $\mathbb{Q}$ with integral
coefficients has rational coordinates, then its $x$-coordinate has nonnegative
$p$-adic valuation at every prime $p$. -/
section MultiplicationByN
end MultiplicationByN
/-- Axiom: a nonconstant morphism of curves $f : E \to E$ sending $0$ to $0$ is
surjective (a curve of genus one has no nontrivial subvariety of dimension one). -/
section Theorem248
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]
/-- Restatement of `mulByN_surjective_axiom` for use inside the
`Theorem248` section. -/
end Theorem248
section Corollary2410
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]
/-- Corollary 24.10: the $n$-torsion subgroup $E[n] \subseteq E(F)$ is finite. -/
end Corollary2410

/--
[PadicFiltrationMem.of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma PadicFiltrationMem.of_le
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n m : ℕ}
  {P : (W.baseChange ℚ_[p]).toAffine.Point}
-- given
  (h : PadicFiltrationMem W p n P)
  (hmn : m ≤ n) :
-- imply
  PadicFiltrationMem W p m P := by
-- proof
  match P with
  | .zero => trivial
  | .some x y hxy =>
    simp only [PadicFiltrationMem] at h ⊢
    obtain rfl | hm := Nat.eq_zero_or_pos m
    · exact Or.inl rfl
    · right
      obtain rfl | ⟨hy, hv⟩ := h
      · omega
      · exact ⟨hy, le_trans (by exact_mod_cast hmn) hv⟩
noncomputable section
open Classical

/--
[padic_valuation_add_eq_min](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma padic_valuation_add_eq_min
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {x y : ℚ_[p]}
-- given
  (hxy : x + y ≠ 0)
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hv : Padic.valuation x ≠ Padic.valuation y) :
-- imply
  Padic.valuation (x + y) = min (Padic.valuation x) (Padic.valuation y) := by
-- proof
  have h1 := Padic.le_valuation_add hxy
  have h2 : min (Padic.valuation (x + y)) (Padic.valuation y) ≤ Padic.valuation x := by
    have h := Padic.le_valuation_add (show (x + y) + (-y) ≠ 0 by rwa [add_neg_cancel_right])
    rwa [padic_valuation_neg y hy, add_neg_cancel_right] at h
  have h3 : min (Padic.valuation (x + y)) (Padic.valuation x) ≤ Padic.valuation y := by
    have h := Padic.le_valuation_add (show (x + y) + (-x) ≠ 0 by
      rwa [show (x + y) + (-x) = y from by ring])
    rwa [padic_valuation_neg x hx, show (x + y) + (-x) = y from by ring] at h
  omega

/--
[padic_valuation_sub_eq_min](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma padic_valuation_sub_eq_min
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {x y : ℚ_[p]}
-- given
  (hxy : x - y ≠ 0)
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hv : Padic.valuation x ≠ Padic.valuation y) :
-- imply
  Padic.valuation (x - y) = min (Padic.valuation x) (Padic.valuation y) := by
-- proof
  rw [sub_eq_add_neg] at hxy ⊢
  rw [padic_valuation_add_eq_min hxy hx (neg_ne_zero.mpr hy)
    (by rwa [padic_valuation_neg y hy]),
    padic_valuation_neg y hy]

/--
[PadicFiltration.exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma PadicFiltration.exists
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (ha₁ : W.a₁ = 0)
  (ha₂ : W.a₂ = 0)
  (ha₃ : W.a₃ = 0) :
-- imply
  Nonempty (PadicFiltration W p) := by
-- proof
  exact ⟨{
    group := padicFiltrationGroup W ha₁ ha₂ ha₃ p
    antitone := by
      intro m n hmn P hP
      show PadicFiltrationMem W p m P
      have hPn : PadicFiltrationMem W p n P := hP
      exact PadicFiltrationMem.of_le hPn hmn
    mem_iff := by
      intro n P
      exact Iff.rfl
    zero_eq_top := by
      ext P
      simp only [AddSubgroup.mem_top, iff_true]
      show PadicFiltrationMem W p 0 P
      match P with
      | .zero => trivial
      | .some x y _ => exact Or.inl rfl
    ha₁ := ha₁
    ha₂ := ha₂
    ha₃ := ha₃
  }⟩
namespace PadicFiltration
variable {W : WeierstrassCurve ℚ} [W.IsElliptic]
variable {p : ℕ} [Fact (Nat.Prime p)]
variable (F : PadicFiltration W p)

namespace PadicFiltration

/--
[padicFiltrationMem_iff_inPadicFiltration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma padicFiltrationMem_iff_inPadicFiltration
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {F : PadicFiltration W p}
  {n : ℕ}
  {P : (W.baseChange ℚ_[p]).toAffine.Point}
-- given
  (hn : 0 < n) :
-- imply
  PadicFiltrationMem W p n P ↔ PadicElliptic.InPadicFiltration W n P := by
-- proof
  match P with
  | .zero => simp [PadicFiltrationMem, PadicElliptic.InPadicFiltration]
  | .some x y _ =>
    simp only [PadicFiltrationMem, PadicElliptic.InPadicFiltration]
    constructor
    · intro h
      obtain rfl | h := h
      · omega
      · exact h
    · exact Or.inr

end PadicFiltration

namespace PadicFiltration

/--
[group_eq_padicFiltration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma group_eq_padicFiltration
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {F : PadicFiltration W p}
  {n : ℕ}
-- given
  (ha1 : W.a₁ = 0)
  (ha2 : W.a₂ = 0)
  (ha3 : W.a₃ = 0)
  (hn : 0 < n) :
-- imply
  F.group n = PadicElliptic.padicFiltration W ha1 ha2 ha3 n := by
-- proof
  ext P
  rw [F.mem_iff n P, padicFiltrationMem_iff_inPadicFiltration n hn P]
  rfl

end PadicFiltration

namespace PadicFiltration

/--
[iInf_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma iInf_eq_bot
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {F : PadicFiltration W p} :
-- imply
  ⨅ n, F.group n = ⊥ := by
-- proof
  rw [eq_bot_iff]
  intro P hP
  rw [AddSubgroup.mem_iInf] at hP
  rw [AddSubgroup.mem_bot]
  match P with
  | .zero => rfl
  | .some x y hxy =>
    exfalso
    have hmem : ∀ n : ℕ, PadicFiltrationMem W p n (.some x y hxy) := fun n =>
      (F.mem_iff n _).mp (hP n)
    have hval : ∀ k : ℕ, (k.succ : ℤ) ≤ Padic.valuation x - Padic.valuation y := by
      intro k
      obtain h | ⟨_, hv⟩ := hmem k.succ
      · exact absurd h (Nat.succ_ne_zero k)
      · exact hv
    have : ¬ (∀ k : ℕ, (k.succ : ℤ) ≤ Padic.valuation x - Padic.valuation y) := by
      push Not
      exact ⟨(Padic.valuation x - Padic.valuation y).toNat, by omega⟩
    exact this hval
/-- Theorem 24.14 (Reduction theorem for the $p$-adic filtration).
The successive quotients of $E_0 \supseteq E_1 \supseteq E_2 \supseteq \cdots$
are:
\begin{itemize}
  \item $E_0/E_1 \cong \widetilde{E}(\mathbb{F}_p)$ (reduction modulo $p$),
  \item $E_n/E_{n+1} \cong \mathbb{F}_p$ for all $n \geq 1$ (via the formal logarithm),
  \item $\bigcap_n E_n = 0$ (the filtration is separated).
\end{itemize} -/
end PadicFiltration
end
noncomputable section
open Classical


/--
[nsmul_eq_zero_in_zmod_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma nsmul_eq_zero_in_zmod_prime
  {p : ℕ}
  {m : ℕ}
  {x : ZMod p}
-- given
  (hp : Nat.Prime p)
  (hm : Nat.Coprime m p)
  (h : m • x = 0) :
-- imply
  x = 0 := by
-- proof
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [nsmul_eq_mul] at h
  obtain hm0 | hx0 := mul_eq_zero.mp h
  · rw [ZMod.natCast_eq_zero_iff m p] at hm0
    have : p ∣ Nat.gcd m p := Nat.dvd_gcd hm0 (dvd_refl p)
    rw [hm] at this
    exact absurd this (Nat.Prime.not_dvd_one hp)
  · exact hx0

/--
[weierstrass_valuation_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma weierstrass_valuation_bound
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {x y : ℚ_[p]}
-- given
  (h_coeff : 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₆))
  (h : (W.baseChange ℚ_[p]).toAffine.Nonsingular x y)
  (h_not_int : ¬ (0 ≤ Padic.valuation x ∧ 0 ≤ Padic.valuation y)) :
-- imply
  y ≠ 0 ∧ (1 : ℤ) ≤ Padic.valuation x - Padic.valuation y :=
-- proof
  weierstrass_valuation_bound_proof h_coeff h h_not_int

/--
[non_integral_implies_in_filtration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
lemma non_integral_implies_in_filtration
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {F : PadicFiltration W p}
  {P : (W.baseChange ℚ_[p]).toAffine.Point}
-- given
  (h_coeff : 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧ 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₆))
  (h_not_integral : ¬ CoordinatesPadicIntegral P) :
-- imply
  ∃ n : ℕ, 0 < n ∧ P ∈ F.group n ∧ ¬ (∀ k : ℕ, P ∈ F.group k) := by
-- proof
  match P with
  | .zero => exact absurd trivial h_not_integral
  | .some x y hxy =>
    have hval := weierstrass_valuation_bound h_coeff hxy h_not_integral
    have h_in_1 : WeierstrassCurve.Affine.Point.some x y hxy ∈ F.group 1 := by
      rw [F.mem_iff]
      show PadicFiltrationMem W p 1 (.some x y hxy)
      exact Or.inr hval
    have h_ne_zero : WeierstrassCurve.Affine.Point.some x y hxy ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero hxy
    have h_not_all : ¬ (∀ k, WeierstrassCurve.Affine.Point.some x y hxy ∈ F.group k) := by
      intro hall
      have h_in_bot : WeierstrassCurve.Affine.Point.some x y hxy ∈
        (⊥ : AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point) := by
        rw [← F.iInf_eq_bot]
        exact AddSubgroup.mem_iInf.mpr hall
      rw [AddSubgroup.mem_bot] at h_in_bot
      exact h_ne_zero h_in_bot
    exact ⟨1, Nat.one_pos, h_in_1, h_not_all⟩
/-- Corollary 24.16. Let $E$ be an elliptic curve over $\mathbb{Q}$ with
$p$-integral Weierstrass coefficients, and let $P \in E(\mathbb{Q}_p)$. If
$m \cdot P = 0$ for some integer $m$ with $\gcd(m, p) = 1$, then the
coordinates of $P$ are $p$-adically integral. -/
end

/--
[WeierstrassCurve.Affine.Point.toOption_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
private lemma toOption_injective_eq
  [CommRing R]
  [Fintype R]
  {W : WeierstrassCurve R} :
-- imply
  Function.Injective (WeierstrassCurve.Affine.Point.toOption W) := by
-- proof
  apply WeierstrassCurve.Affine.Point.toOption_injective W

/--
[PadicFiltrationMem.zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
private lemma zero_eq
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n : ℕ} :
-- imply
  PadicFiltrationMem W p n (.zero) := by
-- proof
  apply PadicFiltrationMem.zero W p n

/--
[padic_valuation_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
private lemma padic_valuation_neg_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {x : ℚ_[p]}
-- given
  (hx : x ≠ 0) :
-- imply
  Padic.valuation (-x) = Padic.valuation x := by
-- proof
  apply padic_valuation_neg x hx

/--
[PadicFiltrationMem.add_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
private lemma add_mem_eq
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n : ℕ}
  {P Q : (W.baseChange ℚ_[p]).toAffine.Point}
-- given
  (ha₁ : W.a₁ = 0)
  (ha₂ : W.a₂ = 0)
  (ha₃ : W.a₃ = 0)
  (hP : PadicFiltrationMem W p n P)
  (hQ : PadicFiltrationMem W p n Q) :
-- imply
  PadicFiltrationMem W p n (P + Q) := by
-- proof
  apply PadicFiltrationMem.add_mem ha₁ ha₂ ha₃ hP hQ

/--
[PadicFiltrationMem.neg_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean)
-/
@[path]
private lemma neg_mem_eq
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n : ℕ}
  {P : (W.baseChange ℚ_[p]).toAffine.Point}
-- given
  (ha₁ : W.a₁ = 0)
  (ha₃ : W.a₃ = 0)
  (hP : PadicFiltrationMem W p n P) :
-- imply
  PadicFiltrationMem W p n (-P) := by
-- proof
  apply PadicFiltrationMem.neg_mem ha₁ ha₃ hP


-- created on 2026-10-23
