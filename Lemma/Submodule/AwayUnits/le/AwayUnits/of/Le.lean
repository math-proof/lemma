import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Lemma.Int.P2MUtil

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

/--
[CerednikDrinfeld_CosetGraph_awayUnits_mono](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_CosetGraph_awayUnits_mono.lean)
-/

private lemma  localBox_mono' {D : Type*} [Ring D] [Algebra ℚ D] {Λ Λ' : Submodule ℤ D} (h : Λ' ≤ Λ)
  (w : HeightOneSpectrum (𝓞 ℚ)) : Submodule.localBox Λ' w ≤ Submodule.localBox Λ w := by
  apply AddSubgroup.closure_mono
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩
@[path]
private lemma main
  {a b : ℚ}
  {R R' : Submodule ℤ ℍ[ℚ, a, b]}
  {v : HeightOneSpectrum (𝓞 ℚ)}
-- given
  (h : R' ≤ R) :
-- imply
  CosetGraph.awayUnits R' v ≤ CosetGraph.awayUnits R v := by
-- proof
  intro x hx
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => Subgroup.mem_comap.2 ?_
  have hx' : CosetGraph.toLoc w x ∈ Subgroup.closure (Submodule.localBoxUnits R' w) :=
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx w) hw)
  refine Subgroup.closure_mono ?_ hx'
  rintro u ⟨hu, hu'⟩
  exact ⟨localBox_mono' h w hu, localBox_mono' h w hu'⟩


-- created on 2026-10-23
