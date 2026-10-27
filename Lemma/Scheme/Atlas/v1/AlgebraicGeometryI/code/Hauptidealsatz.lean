import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped nonZeroDivisors


namespace Hauptidealsatz

/--
[dim_quotient_ge_dim_minus_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Hauptidealsatz.lean)
-/
@[path]
lemma dim_quotient_ge_dim_minus_one
  [CommRing R]
  [IsDomain R]
  {g : R}
-- given
  (hg : g ≠ 0) :
-- imply
  ringKrullDim (R ⧸ Ideal.span {g}) + 1 ≤ ringKrullDim R :=
-- proof
  ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg)

end Hauptidealsatz

namespace Hauptidealsatz

/--
[height_eq_one_of_mem_minimalPrimes_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Hauptidealsatz.lean)
-/
@[path]
lemma height_eq_one_of_mem_minimalPrimes_principal
  [CommRing R]
  [IsDomain R]
  [IsNoetherianRing R]
  {g : R}
  {p : Ideal R}
  [p.IsPrime]
-- given
  (hg : g ≠ 0)
  (_hg_unit : ¬IsUnit g)
  (hp : p ∈ (Ideal.span {g}).minimalPrimes) :
-- imply
  p.height = 1 := by
-- proof
  have h_le : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp
  have h_ge : 1 ≤ p.height := by
    rw [Ideal.height_eq_primeHeight, ENat.one_le_iff_ne_zero]
    intro h0
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff] at h0
    have hgp : g ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton g))
    rw [h0] at hgp
    exact hg (Ideal.mem_bot.mp hgp)
  exact le_antisymm h_le h_ge

end Hauptidealsatz


-- created on 2026-10-23
