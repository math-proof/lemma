import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.PontryaginDual
open MetaMathlibExt


/--
[PadicPontryaginDual_ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
private lemma PadicPontryaginDual_ext_eq
  [AddCommGroup A]
  {p : ℕ} [Fact p.Prime] [Module ℤ_[p] A]
  {φ ψ : PadicPontryaginDual p A}
-- given
  (h : ∀ a, φ a = ψ a) :
-- imply
  φ = ψ := by
-- proof
  apply MetaMathlibExt.PadicPontryaginDual_ext h

/--
[padicQuotientMap_algebraMap_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
private lemma padicQuotientMap_algebraMap_eq_zero_eq
  {p : ℕ} [Fact p.Prime]
  {z : ℤ_[p]} :
-- imply
  padicQuotientMap p (algebraMap ℤ_[p] ℚ_[p] z) = 0 := by
-- proof
  apply MetaMathlibExt.padicQuotientMap_algebraMap_eq_zero p z

/--
[padicQuotientMap_mkQ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
private lemma padicQuotientMap_mkQ_eq_eq
  {p : ℕ} [Fact p.Prime]
  {x : ℚ_[p]} :
-- imply
  padicQuotientMap p x = Submodule.Quotient.mk x := by
-- proof
  apply MetaMathlibExt.padicQuotientMap_mkQ_eq p x

/--
[smul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
private lemma smul_apply_eq
  [Group G] [AddCommGroup A] [DistribMulAction G A]
  {p : ℕ} [Fact p.Prime] [Module ℤ_[p] A] [SMulCommClass G ℤ_[p] A]
  {g : G}
  {φ : PadicPontryaginDual p A}
  {a : A} :
-- imply
  (g • φ) a = φ (g⁻¹ • a) := by
-- proof
  apply MetaMathlibExt.smul_apply p G A g φ a


-- created on 2026-10-20
