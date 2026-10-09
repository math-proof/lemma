import Mathlib
import sympy.Basic
import sympy.Algebra.Module.KaplanskyProjective

open Kaplansky

/--
[kap_projective_of_retract](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma projective_of_retract
  [Ring R] [AddCommGroup M] [Module R M] [Module.Projective R M]
-- given
  (N : Submodule R M) (f : M →ₗ[R] M)
  (hmem : ∀ x, f x ∈ N) (hid : ∀ x : ↥N, f (x : M) = (x : M)) :
-- imply
  Module.Projective R ↥N := by
-- proof
  apply kap_projective_of_retract N f hmem hid


/--
[kap_isUnit_det_of_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma isUnit_det_of_sub_one
  [CommRing R] [IsLocalRing R]
  [Fintype κ] [DecidableEq κ]
-- given
  (A : Matrix κ κ R)
  (h : ∀ i j, A i j - (1 : Matrix κ κ R) i j ∈ IsLocalRing.maximalIdeal R) :
-- imply
  IsUnit A.det := by
-- proof
  apply kap_isUnit_det_of_sub_one A h


/--
[kap_isCompl_sup_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma isCompl_sup_map
  [Ring R] [AddCommGroup M] [Module R M]
-- given
  (A D : Submodule R M) (B E : Submodule R ↥D)
  (h : IsCompl A D) (hBE : IsCompl B E) :
-- imply
  IsCompl (A ⊔ B.map D.subtype) (E.map D.subtype) := by
-- proof
  apply kap_isCompl_sup_map A D h B E hBE


/--
[kap_exists_countable_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma exists_countable_closed
  [CommRing R] [AddCommGroup M] [Module R M]
-- given
  (s : M →ₗ[R] (Finsupp M R)) (m : M) :
-- imply
  ∃ J₁ : Set M, J₁.Countable ∧ m ∈ J₁ ∧ ∀ p ∈ J₁, ↑(s p).support ⊆ J₁ := by
-- proof
  apply kap_exists_countable_closed s m


/--
[kap_content_ideal_facts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma content_ideal_facts
  [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
-- given
  (s : M →ₗ[R] (Finsupp M R))
  (hs : LinearMap.comp (Finsupp.linearCombination R id) s = LinearMap.id)
  (x : M) :
-- imply
  (LinearMap.range (Module.Dual.eval R M x)).FG ∧
    (∀ m : M, s x m ∈ LinearMap.range (Module.Dual.eval R M x)) ∧
    x = ∑ m ∈ (s x).support, (s x m) • m := by
-- proof
  apply kap_content_ideal_facts s hs x


/--
[kap_exists_minimal_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma exists_minimal_span
  [CommRing R] [IsLocalRing R] [AddCommGroup M'] [Module R M']
-- given
  (N : Submodule R M')
  (hN : N.FG) :
-- imply
  ∃ S : Finset M', Submodule.span R (↑S : Set M') = N ∧
    ∀ r : M' → R, (∑ a ∈ S, r a • a = 0) → ∀ a ∈ S, r a ∈ IsLocalRing.maximalIdeal R := by
-- proof
  apply kap_exists_minimal_span N hN


/--
[kap_free_summand_of_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma free_summand_of_pairing
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [Finite κ] [DecidableEq κ]
-- given
  (z : κ → M) (ψ : κ → Module.Dual R M)
  (h : ∀ j k, ψ k (z j) - (if j = k then 1 else 0) ∈ IsLocalRing.maximalIdeal R) :
-- imply
  LinearIndependent R z ∧
    ∃ D : Submodule R M, IsCompl (Submodule.span R (Set.range z)) D := by
-- proof
  apply kap_free_summand_of_pairing z ψ h


/--
[kap_exists_free_summand_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma exists_free_summand_mem
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
-- given
  (x : M) :
-- imply
  ∃ u : Set M, LinearIndepOn R id u ∧ (∃ D : Submodule R M, IsCompl (Submodule.span R u) D)
    ∧ x ∈ Submodule.span R u := by
-- proof
  apply kap_exists_free_summand_mem x


/--
[kap_kapProj_facts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma kapProj_facts
  [CommRing R] [AddCommGroup M] [Module R M]
-- given
  (s : M →ₗ[R] (Finsupp M R))
  (hs : LinearMap.comp (Finsupp.linearCombination R id) s = LinearMap.id)
  (J : Set M) :
-- imply
  (∀ x, kapProj s J x ∈ Submodule.span R J) ∧
    ((∀ p ∈ J, ↑(s p).support ⊆ J) → ∀ x ∈ Submodule.span R J, kapProj s J x = x) := by
-- proof
  apply kap_kapProj_facts s hs J


/--
[kap_extend_free_summand](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma extend_free_summand
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
-- given
  (u : Set M) (D : Submodule R M)
  (hli : LinearIndepOn R id u) (hD : IsCompl (Submodule.span R u) D)
  (x : M) :
-- imply
  ∃ u' : Set M, ∃ D' : Submodule R M, u ⊆ u' ∧ LinearIndepOn R id u' ∧
    IsCompl (Submodule.span R u') D' ∧ x ∈ Submodule.span R u' := by
-- proof
  apply kap_extend_free_summand u hli D hD x


/--
[kap_free_of_projective_of_countable_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma free_of_projective_of_countable_span
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
-- given
  (g : Set M)
  (hgcount : g.Countable) (hgspan : Submodule.span R g = ⊤) :
-- imply
  Module.Free R M := by
-- proof
  apply kap_free_of_projective_of_countable_span g hgcount hgspan


/--
[kap_exists_basis_of_countable_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma exists_basis_of_countable_span
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  {N : Submodule R M} [Module.Projective R ↥N]
-- given
  (T : Set M)
  (hTcount : T.Countable) (hTspan : Submodule.span R T = N) :
-- imply
  ∃ c : Set M, LinearIndepOn R id c ∧ Submodule.span R c = N := by
-- proof
  apply kap_exists_basis_of_countable_span N T hTcount hTspan


/--
[kap_closed_complement_facts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma closed_complement_facts
  [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
-- given
  (s : M →ₗ[R] (Finsupp M R)) (J J₁ : Set M)
  (hs : LinearMap.comp (Finsupp.linearCombination R id) s = LinearMap.id)
  (hJ : ∀ p ∈ J, ↑(s p).support ⊆ J) (hJ₁ : ∀ p ∈ J₁, ↑(s p).support ⊆ J₁) :
-- imply
  Disjoint (Submodule.span R J)
    (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) ∧
    Submodule.span R J ⊔ (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) =
      Submodule.span R (J ∪ J₁) ∧
    Module.Projective R ↥(Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) ∧
    (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) =
      Submodule.span R (((LinearMap.id - kapProj s J : M →ₗ[R] M)) '' J₁) := by
-- proof
  apply kap_closed_complement_facts s hs J J₁ hJ hJ₁


/--
[kap_extend_closed_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma extend_closed_pair
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
-- given
  (s : M →ₗ[R] (Finsupp M R)) (J b : Set M)
  (hs : LinearMap.comp (Finsupp.linearCombination R id) s = LinearMap.id)
  (hJ : ∀ p ∈ J, ↑(s p).support ⊆ J)
  (hb : LinearIndepOn R id b) (hbspan : Submodule.span R b = Submodule.span R J)
  (m : M) :
-- imply
  ∃ J' : Set M, ∃ b' : Set M, (∀ p ∈ J', ↑(s p).support ⊆ J') ∧
    LinearIndepOn R id b' ∧ Submodule.span R b' = Submodule.span R J' ∧
    J ⊆ J' ∧ b ⊆ b' ∧ m ∈ J' := by
-- proof
  apply kap_extend_closed_pair s hs J b hJ hb hbspan m


/--
[kap_projective_local_free_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma projective_local_free_aux
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] :
-- imply
  Module.Free R M := by
-- proof
  apply kap_projective_local_free_aux


/--
[kaplansky_projective_local_free](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/KaplanskyProjective.lean)
-/
@[path]
private lemma projective_local_free
  [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] :
-- imply
  Module.Free R M := by
-- proof
  apply kaplansky_projective_local_free


-- created on 2026-10-09
