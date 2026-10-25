import Mathlib
import sympy.Basic
import Instance.GroupTheory.BurnsidePaqb.ScalarCenter
open BurnsidePaqb


namespace BurnsidePaqb

/--
[all_roots_eq_of_norm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
lemma all_roots_eq_of_norm_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [Finite G]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G}
-- given
  (h : ‖ρ.character g‖ = Module.finrank ℂ V) :
-- imply
  ∀ μ₁ ∈ (ρ g).charpoly.roots, ∀ μ₂ ∈ (ρ g).charpoly.roots, μ₁ = μ₂ := by
-- proof
  by_contra hcon
  push Not at hcon
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, hne⟩ := hcon
  have hlt := abs_multiset_sum_lt _ (fun μ hμ => charpoly_root_norm_eq_one ρ g μ hμ)
    ⟨μ₁, hμ₁, μ₂, hμ₂, hne⟩
  rw [← character_eq_sum_roots ρ g, charpoly_roots_card ρ g] at hlt
  rw [h] at hlt
  exact (lt_irrefl _) hlt

end BurnsidePaqb

namespace BurnsidePaqb

/--
[eq_smul_one_of_all_roots_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
lemma eq_smul_one_of_all_roots_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [Finite G]
  {ρ : Representation ℂ G V}
  {g : G}
  {μ₀ : ℂ}
-- given
  (hall : ∀ μ ∈ (ρ g).charpoly.roots, μ = μ₀) :
-- imply
  (ρ g : Module.End ℂ V) = μ₀ • 1 := by
-- proof
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hn : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have hpow : (ρ g : Module.End ℂ V) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have haeval1 : Polynomial.aeval (ρ g : Module.End ℂ V)
    (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
    exact sub_eq_zero.mpr hpow
  have hdvd1 : minpoly ℂ (ρ g : Module.End ℂ V)
    ∣ (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ) :=
    minpoly.dvd _ _ haeval1
  have hsplit : (ρ g).charpoly.Splits := IsAlgClosed.splits _
  have hprod := hsplit.eq_prod_roots_of_monic (LinearMap.charpoly_monic _)
  have hmap : (ρ g).charpoly.roots.map (fun μ => Polynomial.X - Polynomial.C μ)
    = Multiset.replicate (Module.finrank ℂ V)
      (Polynomial.X - Polynomial.C μ₀) := by
    have hcard := charpoly_roots_card ρ g
    rw [← hcard, ← Multiset.map_const]
    apply Multiset.map_congr rfl
    intro μ hμ
    change Polynomial.X - Polynomial.C μ = Polynomial.X - Polynomial.C μ₀
    rw [hall μ hμ]
  rw [hmap, Multiset.prod_replicate] at hprod
  have hCH : Polynomial.aeval (ρ g : Module.End ℂ V) (ρ g).charpoly = 0 :=
    LinearMap.aeval_self_charpoly _
  have hdvd2 : minpoly ℂ (ρ g : Module.End ℂ V)
    ∣ (Polynomial.X - Polynomial.C μ₀) ^ Module.finrank ℂ V := by
    rw [← hprod]
    exact minpoly.dvd _ _ hCH
  have hsep : (Polynomial.X ^ orderOf g - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hn) one_ne_zero
  have hsep1 : (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ).Separable := by
    have h1 := hsep
    rwa [Polynomial.C_1] at h1
  have hmsep : (minpoly ℂ (ρ g : Module.End ℂ V)).Separable :=
    hsep1.of_dvd hdvd1
  have hdvd3 : minpoly ℂ (ρ g : Module.End ℂ V) ∣ Polynomial.X - Polynomial.C μ₀ :=
    (hmsep.squarefree.dvd_pow_iff_dvd (ne_of_gt hpos)).mp hdvd2
  have hInt : IsIntegral ℂ (ρ g : Module.End ℂ V) :=
    Algebra.IsIntegral.isIntegral _
  have hmonic : (minpoly ℂ (ρ g : Module.End ℂ V)).Monic := minpoly.monic hInt
  have hmonic2 : (Polynomial.X - Polynomial.C μ₀).Monic :=
    Polynomial.monic_X_sub_C μ₀
  have hdeg : (Polynomial.X - Polynomial.C μ₀).natDegree
    ≤ (minpoly ℂ (ρ g : Module.End ℂ V)).natDegree := by
    rw [Polynomial.natDegree_X_sub_C]
    by_contra hlt
    have h0 : (minpoly ℂ (ρ g : Module.End ℂ V)).natDegree = 0 := by omega
    have heq1 : minpoly ℂ (ρ g : Module.End ℂ V) = 1 := by
      have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
      have h1 : (minpoly ℂ (ρ g : Module.End ℂ V)).coeff 0 = 1 := by
        have hlc := Polynomial.Monic.def.mp hmonic
        rwa [hC, Polynomial.leadingCoeff_C] at hlc
      rw [hC, h1, Polynomial.C_1]
    exact minpoly.ne_one _ _ heq1
  have heq : Polynomial.X - Polynomial.C μ₀ = minpoly ℂ (ρ g : Module.End ℂ V) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hmonic2 hdvd3 hdeg
  have haeval : Polynomial.aeval (ρ g : Module.End ℂ V)
    (Polynomial.X - Polynomial.C μ₀) = 0 := by
    rw [heq]
    exact minpoly.aeval _ _
  have hcalc : Polynomial.aeval (ρ g : Module.End ℂ V)
    (Polynomial.X - Polynomial.C μ₀)
    = (ρ g : Module.End ℂ V) - μ₀ • (1 : Module.End ℂ V) := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
  rw [hcalc] at haeval
  exact sub_eq_zero.mp haeval

end BurnsidePaqb

namespace BurnsidePaqb

/--
[mem_charCenter_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
lemma mem_charCenter_iff
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
  {g : G} :
-- imply
  g ∈ charCenter ρ ↔ ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 :=
-- proof
  Iff.rfl

end BurnsidePaqb

namespace BurnsidePaqb

/--
[mem_charCenter_of_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
lemma mem_charCenter_of_eq_smul
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
  {g : G}
  {c : ℂ}
-- given
  (hc : (ρ g : Module.End ℂ V) = c • 1) :
-- imply
  g ∈ charCenter ρ :=
-- proof
  ⟨c, hc⟩

end BurnsidePaqb

namespace BurnsidePaqb

/--
[exists_eq_smul_of_mem_charCenter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
lemma exists_eq_smul_of_mem_charCenter
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (h : g ∈ charCenter ρ) :
-- imply
  ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 :=
-- proof
  h

end BurnsidePaqb

namespace BurnsidePaqb

/--
[charCenter_proper_of_nonlinear](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
lemma charCenter_proper_of_nonlinear
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
-- given
  (h : 1 < Module.finrank ℂ V) :
-- imply
  charCenter ρ ≠ ⊤ := by
-- proof
  intro htop
  have hall : ∀ g : G, ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 := by
    intro g
    have hg : g ∈ charCenter ρ := htop ▸ Subgroup.mem_top g
    exact hg
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hWmem : v ∈ Submodule.span ℂ ({v} : Set V) :=
    Submodule.subset_span (Set.mem_singleton v)
  have hinv : ∀ g : G, ∀ w ∈ Submodule.span ℂ ({v} : Set V),
    (ρ g : Module.End ℂ V) w ∈ Submodule.span ℂ ({v} : Set V) := by
    intro g w hw
    obtain ⟨c, hc⟩ := hall g
    rw [hc, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.smul_mem _ c hw
  let S : Subrepresentation ρ :=
    ⟨Submodule.span ℂ ({v} : Set V), fun g _ hw => hinv g _ hw⟩
  have hSmod : S.toSubmodule = Submodule.span ℂ ({v} : Set V) := rfl
  have hbot : S ≠ ⊥ := by
    intro hS
    have h2 : S.toSubmodule = ⊥ := by rw [hS]; rfl
    rw [hSmod] at h2
    rw [h2] at hWmem
    exact hv ((Submodule.mem_bot ℂ).mp hWmem)
  have htopS : S ≠ ⊤ := by
    intro hS
    have h2 : S.toSubmodule = ⊤ := by rw [hS]; rfl
    rw [hSmod] at h2
    have hfin : Module.finrank ℂ (Submodule.span ℂ ({v} : Set V)) = 1 :=
      finrank_span_singleton hv
    have hfinW : Module.finrank ℂ (Submodule.span ℂ ({v} : Set V))
      = Module.finrank ℂ V := by
      rw [h2]
      exact finrank_top ℂ V
    omega
  exact hbot (eq_bot_or_eq_top S |>.resolve_right htopS)

end BurnsidePaqb

namespace BurnsidePaqb

/--
[norm_eq_of_mem_charCenter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
lemma norm_eq_of_mem_charCenter
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [Finite G]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (h : g ∈ charCenter ρ) :
-- imply
  ‖ρ.character g‖ = Module.finrank ℂ V := by
-- proof
  obtain ⟨c, hc⟩ := h
  have hn : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have hpow : (ρ g : Module.End ℂ V) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hcpow : c ^ orderOf g = 1 := by
    have hpow' : (c ^ orderOf g) • (1 : Module.End ℂ V) = 1 := by
      have h2 := hpow
      rwa [hc, smul_pow, one_pow] at h2
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1v : c ^ orderOf g • v = v := by
      have h3 := congrArg (· v) hpow'
      simpa using h3
    have h4 : (c ^ orderOf g - 1) • v = 0 := by
      rw [sub_smul, h1v, one_smul, sub_self]
    obtain h5 | h5 := smul_eq_zero.mp h4
    · exact sub_eq_zero.mp h5
    · exact absurd h5 hv
  have hc1 : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hcpow hn
  have htr : ρ.character g = (Module.finrank ℂ V : ℂ) * c := by
    change LinearMap.trace ℂ V (ρ g) = _
    rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]
  rw [htr, norm_mul, hc1, Complex.norm_natCast, mul_one]

end BurnsidePaqb


-- created on 2026-10-20
-- updated on 2026-10-23
