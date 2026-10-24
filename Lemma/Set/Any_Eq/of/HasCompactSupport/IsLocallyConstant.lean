import Mathlib
import sympy.Basic
open Filter Topology Set


private lemma exists_nhds_fourfold
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {Y : Type*}
  [Zero Y]
  {f : G → Y} (hf : IsLocallyConstant f) (g : G) :
  ∃ V ∈ 𝓝 (1 : G), ∀ u ∈ V, ∀ v ∈ V, ∀ v' ∈ V, ∀ u' ∈ V, f (u * v * g * v' * u') = f g := by
  have hc : Continuous fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2 := by fun_prop
  have ho : IsOpen ((fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2) ⁻¹' {x | f x = f g}) :=
    (hf.isOpen_fiber (f g)).preimage hc
  have hmem : ((1 : G), (1 : G), (1 : G), (1 : G))
    ∈ (fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2) ⁻¹' {x | f x = f g} := by
    simp
  have hn := ho.mem_nhds hmem
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hn
  obtain ⟨A₂, hA₂, B₂, hB₂, hAB₂⟩ := mem_nhds_prod_iff.1 hB
  obtain ⟨A₃, hA₃, A₄, hA₄, hAB₃⟩ := mem_nhds_prod_iff.1 hB₂
  refine ⟨A ∩ A₂ ∩ A₃ ∩ A₄, inter_mem (inter_mem (inter_mem hA hA₂) hA₃) hA₄, ?_⟩
  intro u hu v hv v' hv' u' hu'
  have : (u, v, v', u') ∈ (fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2) ⁻¹'
    {x | f x = f g} :=
    hAB ⟨hu.1.1.1, hAB₂ ⟨hv.1.1.2, hAB₃ ⟨hv'.1.2, hu'.2⟩⟩⟩
  simpa using this

private lemma exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport_impl
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {Y : Type*}
  [Zero Y]
  {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) :
  ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, f (u * g * u') = f g := by
  classical
  choose V hV hV4 using exists_nhds_fourfold hf
  set O : G → Set G := fun g => (fun p : G × G => p.1 * g * p.2) '' (V g ×ˢ V g) with hO
  have hOn : ∀ g, O g ∈ 𝓝 g := by
    intro g
    have h1 : (fun v => v * g) '' V g ∈ 𝓝 (1 * g) := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds (hV g)
    rw [one_mul] at h1
    refine mem_of_superset h1 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨(v, 1), ⟨hv, mem_of_mem_nhds (hV g)⟩, by simp⟩
  obtain ⟨t, ht⟩ := hsupp.isCompact.elim_nhds_subcover O (fun g _ => hOn g)
  set V₀ : Set G := ⋂ g ∈ t, V g with hV₀
  have hV₀n : V₀ ∈ 𝓝 (1 : G) := (biInter_finset_mem t).2 fun g _ => hV g
  have hV₀sub : ∀ g ∈ t, V₀ ⊆ V g := fun g hg => biInter_subset_of_mem hg
  have hU : ∀ h ∈ ⋃ g ∈ t, O g, ∀ u ∈ V₀, ∀ u' ∈ V₀, f (u * h * u') = f h := by
    intro h hh u hu u' hu'
    simp only [mem_iUnion] at hh
    obtain ⟨g, hg, hhO⟩ := hh
    obtain ⟨⟨v, v'⟩, ⟨hv, hv'⟩, rfl⟩ := hhO
    have e1 := hV4 g u (hV₀sub g hg hu) v hv v' hv' u' (hV₀sub g hg hu')
    have e2 := hV4 g 1 (mem_of_mem_nhds (hV g)) v hv v' hv' 1 (mem_of_mem_nhds (hV g))
    simp only [one_mul, mul_one] at e2
    calc
      _ = f (u * v * g * v' * u') := by simp only [mul_assoc]
      _ = f g := e1
      _ = f (v * g * v') := e2.symm
  refine ⟨V₀ ∩ V₀⁻¹, inter_mem hV₀n (inv_mem_nhds_one G hV₀n), ?_⟩
  intro u hu u' hu' g
  if h1 : g ∈ ⋃ g ∈ t, O g then
    exact hU g h1 u hu.1 u' hu'.1
  else
    if h2 : u * g * u' ∈ ⋃ g ∈ t, O g then
      have e := hU (u * g * u') h2 u⁻¹ hu.2 u'⁻¹ hu'.2
      have : u⁻¹ * (u * g * u') * u'⁻¹ = g := by simp [mul_assoc]
      rw [this] at e
      apply e.symm
    else
      have hg0 : g ∉ tsupport f := fun h => h1 (ht.2 h)
      have hg1 : u * g * u' ∉ tsupport f := fun h => h2 (ht.2 h)
      rw [image_eq_zero_of_notMem_tsupport hg0, image_eq_zero_of_notMem_tsupport hg1]
private lemma gate_zero
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {Y : Type*}
  [Zero Y]
  : ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, (0 : G → Y) (u * g * u') = (0 : G → Y) g :=
  ⟨univ, univ_mem, fun _ _ _ _ _ => rfl⟩
/--
[IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport.lean)
-/
@[path]
private lemma main
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Zero Y]
  {f : G → Y}
-- given
  (hf : IsLocallyConstant f)
  (hsupp : HasCompactSupport f) :
-- imply
  ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, f (u * g * u') = f g := by
-- proof
  first
    | exact exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport_impl hf hsupp
    | (apply exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport_impl <;> assumption)


-- created on 2026-10-23
