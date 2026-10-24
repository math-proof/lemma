import Mathlib
import sympy.Basic


/--
[span_union_eq_top_of_powers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohModules.lean)
-/
@[path]
lemma span_union_eq_top_of_powers
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {f g : A}
  {S T : Set M}
  {n k : ℕ}
-- given
  (hfg : Ideal.span {f, g} = ⊤)
  (hS : ∀ m : M, f ^ n • m ∈ Submodule.span A S)
  (hT : ∀ m : M, g ^ k • m ∈ Submodule.span A T) :
-- imply
  Submodule.span A (S ∪ T) = ⊤ := by
-- proof
  have hcop : IsCoprime f g := by
    have h1 : (1 : A) ∈ Ideal.span ({f, g} : Set A) := by rw [hfg]; exact Submodule.mem_top
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨a, b, hab⟩ := h1
    exact ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hcop.pow (m := n) (n := k)
  rw [eq_top_iff]
  intro m _
  have key : m = a • (f ^ n • m) + b • (g ^ k • m) := by
    have : (a * f ^ n + b * g ^ k) • m = m := by rw [hab, one_smul]
    rwa [add_smul, mul_smul, mul_smul] at this
  rw [key, Submodule.span_union]
  apply Submodule.add_mem
  · exact (Submodule.span A S ⊔ Submodule.span A T).smul_mem a (Submodule.mem_sup_left (hS m))
  · exact (Submodule.span A S ⊔ Submodule.span A T).smul_mem b (Submodule.mem_sup_right (hT m))

/--
[module_fg_of_localization_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohModules.lean)
-/
@[path]
lemma module_fg_of_localization_fg
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {f g : A}
  {S T : Set M}
  {n k : ℕ}
-- given
  (hfg : Ideal.span {f, g} = ⊤)
  (hSfin : S.Finite)
  (hTfin : T.Finite)
  (hS : ∀ m : M, f ^ n • m ∈ Submodule.span A S)
  (hT : ∀ m : M, g ^ k • m ∈ Submodule.span A T) :
-- imply
  Module.Finite A M := by
-- proof
  rw [Module.finite_def, Submodule.fg_def]
  exact ⟨S ∪ T, hSfin.union hTfin, span_union_eq_top_of_powers hfg hS hT⟩


-- created on 2026-10-23
