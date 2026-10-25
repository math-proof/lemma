import Mathlib
import sympy.Basic
import Def.CerednikDrinfeld_MumfordPeriod
import Lemma.Int.P2MUtil

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

/--
[CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion.lean)
-/
@[path]
private lemma main
  {E V : Type} [Fintype E] [DecidableEq V]
  {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L]
  {ord : Additive Kˣ →+ ℤ}
  {P : PeriodDatum D K L ord}
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∀ t : P.JacPoints, n • t = 0 → ∃ u : ↥P.U, P.π u = t := by
  intro t ht
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective P.periodLattice t
  have hs : s ∈ P.U := by
-- proof
    simp only [PeriodDatum.U, Submodule.mem_comap]
    refine (Submodule.mem_torsion_iff _).mpr
      ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    show (n : ℤ) • P.periodLattice.mkQ s = 0
    rwa [natCast_zsmul]
  exact ⟨⟨s, hs⟩, rfl⟩


-- created on 2026-10-23
