import Mathlib
import sympy.Basic
import Instance.NumberTheory.Padics.PontryaginDual
open MetaMathlibExt


namespace MetaMathlibExt

/--
[PadicPontryaginDual_ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
lemma PadicPontryaginDual_ext
  [AddCommGroup A]
  {p : ℕ} [Fact p.Prime] [Module ℤ_[p] A]
  {φ ψ : PadicPontryaginDual p A}
-- given
  (h : ∀ a, φ a = ψ a) :
-- imply
  φ = ψ :=
-- proof
  LinearMap.ext fun a => h a

end MetaMathlibExt

namespace MetaMathlibExt

/--
[padicQuotientMap_algebraMap_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
lemma padicQuotientMap_algebraMap_eq_zero
  {p : ℕ} [Fact p.Prime]
  {z : ℤ_[p]} :
-- imply
  padicQuotientMap p (algebraMap ℤ_[p] ℚ_[p] z) = 0 := by
-- proof
  unfold padicQuotientMap
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨z, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[smul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
lemma smul_apply
  [Group G] [AddCommGroup A] [DistribMulAction G A]
  {p : ℕ} [Fact p.Prime] [Module ℤ_[p] A] [SMulCommClass G ℤ_[p] A]
  {g : G}
  {φ : PadicPontryaginDual p A}
  {a : A} :
-- imply
  (g • φ) a = φ (g⁻¹ • a) :=
-- proof
  rfl

end MetaMathlibExt

/--
[padicQuotientMap_mkQ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean)
-/
@[path]
lemma padicQuotientMap_mkQ_eq
  {p : ℕ} [Fact p.Prime]
  {x : ℚ_[p]} :
-- imply
  padicQuotientMap p x = Submodule.Quotient.mk x :=
-- proof
  rfl



-- created on 2026-10-20
-- updated on 2026-10-23
