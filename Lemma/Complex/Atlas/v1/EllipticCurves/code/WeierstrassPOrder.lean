import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.EllipticCurves.code.WeierstrassPOrder
open Complex PeriodPair ComplexLattice


namespace ComplexLattice

/--
[weierstrassPFun_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma weierstrassPFun_periodic
  {L : ComplexLattice} :
-- imply
  L.IsLatticePeriodic L.weierstrassPFun := by
-- proof
  intro ω hω z
  show L.weierstrassP (z + ω) = L.weierstrassP z
  exact L.weierstrassP_add_coe z ⟨ω, hω⟩

end ComplexLattice

namespace ComplexLattice

/--
[derivWeierstrassPFun_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma derivWeierstrassPFun_periodic
  {L : ComplexLattice} :
-- imply
  L.IsLatticePeriodic L.derivWeierstrassPFun := by
-- proof
  intro ω hω z
  show L.derivWeierstrassP (z + ω) = L.derivWeierstrassP z
  exact L.derivWeierstrassP_add_coe z ⟨ω, hω⟩

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_isElliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma weierstrassPFun_isElliptic
  {L : ComplexLattice} :
-- imply
  L.IsEllipticFunction L.weierstrassPFun where meromorphic :=
-- proof
  L.weierstrassPFun_meromorphic
    periodic := L.weierstrassPFun_periodic

end ComplexLattice

namespace ComplexLattice

/--
[derivWeierstrassPFun_isElliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma derivWeierstrassPFun_isElliptic
  {L : ComplexLattice} :
-- imply
  L.IsEllipticFunction L.derivWeierstrassPFun where meromorphic :=
-- proof
  L.derivWeierstrassPFun_meromorphic
    periodic := L.derivWeierstrassPFun_periodic

end ComplexLattice

namespace ComplexLattice

/--
[lattice_mem_fundamentalDomain_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma lattice_mem_fundamentalDomain_eq_zero
  {L : ComplexLattice}
  {z : ℂ}
-- given
  (hz_lat : z ∈ L.lattice)
  (hz_fd : z ∈ ZSpan.fundamentalDomain L.basis) :
-- imply
  z = 0 := by
-- proof
  have h1 : ZSpan.fract L.basis z = z := ZSpan.fract_eq_self.mpr hz_fd
  have h2 : ZSpan.fract L.basis (z + 0) = ZSpan.fract L.basis 0 := by
    rw [L.lattice_eq_span_range_basis] at hz_lat
    exact ZSpan.fract_zSpan_add L.basis 0 hz_lat
  simp only [add_zero] at h2
  rw [← h1, h2]
  simp [ZSpan.fract]

end ComplexLattice

namespace ComplexLattice

/--
[poleMultiplicity_weierstrassP_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma poleMultiplicity_weierstrassP_zero
  {L : ComplexLattice} :
-- imply
  poleMultiplicity L.weierstrassPFun 0 = 2 := by
-- proof
  unfold poleMultiplicity
  rw [show meromorphicOrderAt L.weierstrassPFun 0 = ((-2 : ℤ) : WithTop ℤ) from
    L.weierstrassPFun_order 0 L.lattice.zero_mem]
  decide

end ComplexLattice

namespace ComplexLattice

/--
[poleMultiplicity_derivWeierstrassP_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma poleMultiplicity_derivWeierstrassP_zero
  {L : ComplexLattice} :
-- imply
  poleMultiplicity L.derivWeierstrassPFun 0 = 3 := by
-- proof
  unfold poleMultiplicity
  rw [show meromorphicOrderAt L.derivWeierstrassPFun 0 = ((-3 : ℤ) : WithTop ℤ) from
    L.derivWeierstrassPFun_order 0 L.lattice.zero_mem]
  decide

end ComplexLattice

namespace ComplexLattice

/--
[polesInFundParallelogram_weierstrassP_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma polesInFundParallelogram_weierstrassP_eq
  {L : ComplexLattice} :
-- imply
  L.polesInFundParallelogram L.weierstrassPFun 0 = {0} := by
-- proof
  ext z
  simp only [polesInFundParallelogram, fundamentalParallelogram_zero,
    Set.mem_sep_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hz_mem, hz_pole⟩
    by_contra hz_ne
    have hz_not_lattice : z ∉ (L.lattice : Set ℂ) := by
      intro hz_lat
      exact hz_ne (L.lattice_mem_fundamentalDomain_eq_zero z hz_lat hz_mem)
    have h_analytic : AnalyticAt ℂ L.weierstrassPFun z :=
      L.weierstrassPFun_analyticOnNhd z hz_not_lattice
    exact not_lt.mpr h_analytic.meromorphicOrderAt_nonneg hz_pole
  · intro hz_eq
    subst hz_eq
    refine ⟨by rw [ZSpan.mem_fundamentalDomain]; intro i; simp [Set.mem_Ico], ?_⟩
    show meromorphicOrderAt L.weierstrassPFun 0 < 0
    rw [L.weierstrassPFun_order 0 L.lattice.zero_mem]
    show ((-2 : ℤ) : WithTop ℤ) < (0 : ℤ)
    exact_mod_cast (show (-2 : ℤ) < 0 from by norm_num)

end ComplexLattice

namespace ComplexLattice

/--
[polesInFundParallelogram_derivWeierstrassP_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma polesInFundParallelogram_derivWeierstrassP_eq
  {L : ComplexLattice} :
-- imply
  L.polesInFundParallelogram L.derivWeierstrassPFun 0 = {0} := by
-- proof
  ext z
  simp only [polesInFundParallelogram, fundamentalParallelogram_zero,
    Set.mem_sep_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hz_mem, hz_pole⟩
    by_contra hz_ne
    have hz_not_lattice : z ∉ (L.lattice : Set ℂ) := by
      intro hz_lat
      exact hz_ne (L.lattice_mem_fundamentalDomain_eq_zero z hz_lat hz_mem)
    have h_analytic : AnalyticAt ℂ L.derivWeierstrassPFun z :=
      L.derivWeierstrassPFun_analyticOnNhd z hz_not_lattice
    exact not_lt.mpr h_analytic.meromorphicOrderAt_nonneg hz_pole
  · intro hz_eq
    subst hz_eq
    refine ⟨by rw [ZSpan.mem_fundamentalDomain]; intro i; simp [Set.mem_Ico], ?_⟩
    show meromorphicOrderAt L.derivWeierstrassPFun 0 < 0
    rw [L.derivWeierstrassPFun_order 0 L.lattice.zero_mem]
    show ((-3 : ℤ) : WithTop ℤ) < (0 : ℤ)
    exact_mod_cast (show (-3 : ℤ) < 0 from by norm_num)

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_ellipticOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma weierstrassPFun_ellipticOrder
  {L : ComplexLattice} :
-- imply
  ellipticOrder L L.weierstrassPFun L.weierstrassPFun_isElliptic = 2 := by
-- proof
  unfold ellipticOrder
  have h_eq := L.polesInFundParallelogram_weierstrassP_eq
  have h_fin : (polesInFundParallelogram_finite L.weierstrassPFun_isElliptic 0).toFinset =
    {(0 : ℂ)} := by
    ext x; simp [h_eq]
  rw [h_fin]
  simp [L.poleMultiplicity_weierstrassP_zero]

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_sub_const_isElliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma weierstrassPFun_sub_const_isElliptic
  {L : ComplexLattice}
  {c : ℂ} :
-- imply
  L.IsEllipticFunction (fun z => L.weierstrassPFun z - c) where meromorphic :=
-- proof
  L.weierstrassPFun_meromorphic.sub (Meromorphic.const c)
    periodic := by
      intro ω hω z
      simp only
      rw [L.weierstrassPFun_periodic ω hω z]

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_sub_const_order_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma weierstrassPFun_sub_const_order_zero
  {L : ComplexLattice}
  {c : ℂ} :
-- imply
  meromorphicOrderAt (fun z => L.weierstrassPFun z - c) 0 = ((-2 : ℤ) : WithTop ℤ) := by
-- proof
  have h_wp := L.weierstrassPFun_order 0 L.lattice.zero_mem
  have : (fun z => L.weierstrassPFun z - c) = L.weierstrassPFun + (fun _ => -c) := by
    ext z; simp [Pi.add_apply, sub_eq_add_neg]
  rw [this, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-c) 0)]
  · exact h_wp
  · rw [h_wp, meromorphicOrderAt_const]
    split_ifs
    · exact WithTop.coe_lt_top _
    · exact WithTop.coe_lt_coe.mpr (by norm_num : (-2 : ℤ) < 0)

end ComplexLattice

namespace ComplexLattice

/--
[poleMultiplicity_weierstrassP_sub_const_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma poleMultiplicity_weierstrassP_sub_const_zero
  {L : ComplexLattice}
  {c : ℂ} :
-- imply
  poleMultiplicity (fun z => L.weierstrassPFun z - c) 0 = 2 := by
-- proof
  unfold poleMultiplicity
  rw [L.weierstrassPFun_sub_const_order_zero c]
  decide

end ComplexLattice

namespace ComplexLattice

/--
[polesInFundParallelogram_weierstrassP_sub_const_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma polesInFundParallelogram_weierstrassP_sub_const_eq
  {L : ComplexLattice}
  {c : ℂ} :
-- imply
  L.polesInFundParallelogram (fun z => L.weierstrassPFun z - c) 0 = {0} := by
-- proof
  ext z
  simp only [polesInFundParallelogram, fundamentalParallelogram_zero,
    Set.mem_sep_iff, Set.mem_singleton_iff, IsPoleAt]
  constructor
  · intro ⟨hz_mem, hz_pole⟩
    by_contra hz_ne
    have hz_not_lattice : z ∉ (L.lattice : Set ℂ) := by
      intro hz_lat
      exact hz_ne (L.lattice_mem_fundamentalDomain_eq_zero z hz_lat hz_mem)
    have h_analytic : AnalyticAt ℂ (fun z => L.weierstrassPFun z - c) z :=
      (L.weierstrassPFun_analyticOnNhd z hz_not_lattice).sub analyticAt_const
    exact not_lt.mpr h_analytic.meromorphicOrderAt_nonneg hz_pole
  · intro hz_eq
    subst hz_eq
    refine ⟨by rw [ZSpan.mem_fundamentalDomain]; intro i; simp [Set.mem_Ico], ?_⟩
    rw [L.weierstrassPFun_sub_const_order_zero c]
    exact_mod_cast (show (-2 : ℤ) < 0 from by norm_num)

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_sub_const_ellipticOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassPOrder.lean)
-/
@[path]
lemma weierstrassPFun_sub_const_ellipticOrder
  {L : ComplexLattice}
  {c : ℂ} :
-- imply
  ellipticOrder L (fun z => L.weierstrassPFun z - c) (L.weierstrassPFun_sub_const_isElliptic c) = 2 := by
-- proof
  unfold ellipticOrder
  have h_eq := L.polesInFundParallelogram_weierstrassP_sub_const_eq c
  have h_fin : (polesInFundParallelogram_finite
    (L.weierstrassPFun_sub_const_isElliptic c) 0).toFinset = {(0 : ℂ)} := by
    ext x; simp [h_eq]
  rw [h_fin]
  simp [L.poleMultiplicity_weierstrassP_sub_const_zero c]
end ComplexLattice



-- created on 2026-10-23
