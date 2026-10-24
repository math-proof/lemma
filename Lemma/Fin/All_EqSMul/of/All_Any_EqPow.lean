import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Lemma.Int.P2MUtil

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

/--
[CerednikDrinfeld_Mumford_PeriodDatum_U_divisible](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible.lean)
-/
@[path]
private lemma main
  {E V : Type} [Fintype E] [DecidableEq V]
  {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L]
  {ord : Additive Kˣ →+ ℤ}
  {P : PeriodDatum D K L ord}
-- given
  (hroots : ∀ (x : Lˣ) (n : ℕ), 0 < n → ∃ y : Lˣ, y ^ n = x) :
-- imply
  ∀ u : ↥P.U, ∀ n : ℕ, 0 < n → ∃ u' : ↥P.U, n • u' = u := by
  intro u n hn
  obtain ⟨m, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ E) (ribbonKernel D)
  have hex : ∀ i : Fin m, ∃ y : Additive Lˣ, n • y = (u : P.TorusPoints) (b i) := by
-- proof
    intro i
    obtain ⟨y, hy⟩ := hroots (Additive.toMul ((u : P.TorusPoints) (b i))) n hn
    exact ⟨Additive.ofMul y, by rw [← ofMul_pow, hy, ofMul_toMul]⟩
  choose r hr using hex
  let ψ : P.TorusPoints := b.constr ℤ r
  have hψ : n • ψ = (u : P.TorusPoints) := by
    refine b.ext fun i => ?_
    rw [LinearMap.smul_apply, b.constr_basis ℤ r i, hr]
  have hψU : ψ ∈ P.U := by
    have hu := u.2
    simp only [PeriodDatum.U, Submodule.mem_comap] at hu ⊢
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff _).mp hu
    have hau' : a • P.periodLattice.mkQ (u : P.TorusPoints) = 0 := hau
    refine (Submodule.mem_torsion_iff _).mpr
      ⟨⟨a * (n : ℤ), mem_nonZeroDivisors_of_ne_zero
        (mul_ne_zero (nonZeroDivisors.ne_zero ha) (by exact_mod_cast hn.ne'))⟩, ?_⟩
    show (a * (n : ℤ)) • P.periodLattice.mkQ ψ = 0
    rw [mul_smul, natCast_zsmul, ← map_nsmul, hψ, hau']
  refine ⟨⟨ψ, hψU⟩, ?_⟩
  apply Subtype.ext
  exact hψ


-- created on 2026-10-23
