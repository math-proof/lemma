import Lemma.ModularCurve.ModuliPoint
import Def.ModularCurve_SupersingularModuli

set_option autoImplicit false

namespace ModularCurve


theorem mem_ssJSet_iff {p : ℕ} {K : Type*} [Field K] [DecidableEq K] {j : K} :
    j ∈ ssJSet p K ↔ ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
      ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  Iff.rfl


theorem mem_ssLocus_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {x : ModuliPoint N K} :
    x ∈ ssLocus p N K ↔ x.j ∈ ssJSet p K :=
  Iff.rfl

theorem isSupersingular_mk_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {P : Gamma0Pair N K} :
    ModuliPoint.IsSupersingular p (Quot.mk _ P : ModuliPoint N K) ↔
      P.toCurve.j ∈ ssJSet p K :=
  Iff.rfl

end ModularCurve
