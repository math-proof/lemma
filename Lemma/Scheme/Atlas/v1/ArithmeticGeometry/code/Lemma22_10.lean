import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.AdelePlusFDim
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AdelePlusFDim
open FunctionFieldAdeleRing DiscreteValuationFamily
open scoped RestrictedProduct


/--
[dvf_ord_ne_top_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_10.lean)
-/
@[path]
lemma dvf_ord_ne_top_of_ne_zero
  [Field F]
  {k : Type*}
  [Field k]
  [Algebra k F]
  [DiscreteValuationFamily P F k]
  {p : P}
  {x : F}
-- given
  (hx : x ≠ 0) :
-- imply
  DiscreteValuationFamily.ord (k := k) p x ≠ ⊤ := by
-- proof
  intro h
  have hmul := DiscreteValuationFamily.ord_mul (k := k) p x x⁻¹
  rw [mul_inv_cancel₀ hx] at hmul
  have hone : DiscreteValuationFamily.ord (k := k) p (1 : F) = (0 : ℤ) := by
    have := DiscreteValuationFamily.ord_algebraMap (k := k) (F := F) p (1 : k) one_ne_zero
    rwa [map_one] at this
  rw [hone, h] at hmul
  simp at hmul

/--
[dvf_ord_eq_coe_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_10.lean)
-/
@[path]
lemma dvf_ord_eq_coe_of_ne_zero
  [Field F]
  {k : Type*}
  [Field k]
  [Algebra k F]
  [DiscreteValuationFamily P F k]
  {p : P}
  {x : F}
-- given
  (hx : x ≠ 0) :
-- imply
  ∃ n : ℤ, DiscreteValuationFamily.ord (k := k) p x = ↑n := by
-- proof
  cases hv : DiscreteValuationFamily.ord (k := k) p x with
  | top => exact absurd hv (dvf_ord_ne_top_of_ne_zero k p x hx)
  | coe n => exact ⟨n, rfl⟩
/-- Adele covering: any adele $\alpha \in \mathbb{A}_F$ and divisor $D$ admit a divisor $D' \ge D$
such that $\alpha$ lies in the adele subspace $A(D')$. The covering divisor is built from the
component-wise orders of $\alpha$ together with the cofinite vanishing of its negative parts. -/
section Lemma22_10
variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

/--
[riemannDefect_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_10.lean)
-/
@[path]
lemma riemannDefect_mono
  [Field F]
  [DecidableEq P]
  {D D' : P →₀ ℤ}
-- given
  (h : ∀ p, D p ≤ D' p) :
-- imply
  riemannDefect (F := F) (O := O) k D ≤ riemannDefect (F := F) (O := O) k D' := by
-- proof
  have h_dim := AF_subspace_dim (F := F) (O := O) k D D' h
  obtain ⟨_, h_dim_eq⟩ := h_dim
  have h_nn : (0 : ℤ) ≤ ↑(Module.finrank k
    (↥(AF_subspace (F := F) (O := O) k ⇑D') ⧸
      Submodule.comap (AF_subspace (F := F) (O := O) k ⇑D').subtype
        (AF_subspace (F := F) (O := O) k ⇑D))) := Int.natCast_nonneg _
  linarith

/--
[submodule_eq_of_finrank_quotient_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_10.lean)
-/
@[path]
lemma submodule_eq_of_finrank_quotient_zero
  [Field F]
  [DecidableEq P]
  [DivisionRing R]
  [AddCommGroup M]
  [Module R M]
  {S T : Submodule R M}
  [hFD : FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype S)]
-- given
  (hST : S ≤ T)
  (h0 : Module.finrank R (↥T ⧸ Submodule.comap T.subtype S) = 0) :
-- imply
  S = T := by
-- proof
  have hforall := finrank_zero_iff_forall_zero.mp h0
  ext x
  constructor
  · exact fun hx => hST hx
  · intro hx
    have := hforall (Submodule.Quotient.mk (⟨x, hx⟩ : T))
    rw [Submodule.Quotient.mk_eq_zero] at this
    rwa [Submodule.mem_comap, Submodule.subtype_apply] at this
/-- Lemma 22.10: if the Riemann defect of $D$ equals $g - 1$ (i.e. attains the maximum), then the
adele subspace $A(D)$ exhausts the entire adele ring: $A(D) = \mathbb{A}_F$. Equivalently,
$A = A(D) + F$ in the original formulation. The proof combines the covering lemma with the
finite-quotient identification $S = T$ when their quotient has dimension $0$. -/
end Lemma22_10


-- created on 2026-10-23
