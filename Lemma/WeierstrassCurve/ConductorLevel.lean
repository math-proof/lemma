import Mathlib
import Instance.WeierstrassCurve_ConductorLevel
import Def.WeierstrassCurve_ConductorLevel

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

open UniqueFactorizationMonoid


theorem conductorLevel_pos (W : WeierstrassCurve ℤ) : 0 < W.conductorLevel :=
  Nat.radical_pos _

theorem squarefree_conductorLevel (W : WeierstrassCurve ℤ) : Squarefree W.conductorLevel :=
  squarefree_radical

theorem prime_dvd_conductorLevel_iff (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {q : ℕ}
    (hq : q.Prime) : q ∣ W.conductorLevel ↔ (q : ℤ) ∣ W.Δ := by
  rw [conductorLevel, dvd_radical_iff_of_irreducible hq.prime.irreducible
    (Int.natAbs_ne_zero.mpr hΔ)]
  exact Int.natCast_dvd.symm

end WeierstrassCurve

end
