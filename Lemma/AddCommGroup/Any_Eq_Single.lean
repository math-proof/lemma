import Mathlib
import sympy.Basic


/--
[AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single.lean)
-/
@[main]
private lemma main
  [CommRing S] [IsDomain S] [AddCommGroup G]
  {f : AddMonoidAlgebra S G →ₐc[S] AddMonoidAlgebra S G} :
-- imply
  ∃ M : G →+ G, ∀ g : G, f (AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single (M g) 1 := by
-- proof
  classical

  have hgl1 : ∀ g : G, IsGroupLikeElem S (AddMonoidAlgebra.single g (1 : S) : AddMonoidAlgebra S G) := by
    intro g
    refine ⟨?_, ?_⟩
    · rw [AddMonoidAlgebra.counit_single, CommSemiring.counit_apply]
    ·
      rw [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
      rfl
  have hgl : ∀ g : G, IsGroupLikeElem S (f (AddMonoidAlgebra.single g 1)) := fun g => (hgl1 g).map f

  have key : ∀ y : AddMonoidAlgebra S G, IsGroupLikeElem S y → ∃ h, y = AddMonoidAlgebra.single h 1 := by
    intro y hy
    by_contra hne
    push_neg at hne
    have hli := linearIndepOn_isGroupLikeElem (R := S) (A := AddMonoidAlgebra S G)

    have hB : Set.range (fun h : G => (AddMonoidAlgebra.single h (1 : S) : AddMonoidAlgebra S G)) ⊆
        {a | IsGroupLikeElem S a} := by
      rintro _ ⟨h, rfl⟩; exact hgl1 h
    have hyB : y ∉ Set.range (fun h : G => (AddMonoidAlgebra.single h (1 : S) : AddMonoidAlgebra S G)) := by
      rintro ⟨h, rfl⟩; exact hne h rfl
    have hspan : y ∈ Submodule.span S (Set.range (fun h : G =>
        (AddMonoidAlgebra.single h (1 : S) : AddMonoidAlgebra S G))) := by
      refine Submodule.span_mono ?_ (AddMonoidAlgebra.mem_span_support y)
      rintro _ ⟨h, -, rfl⟩
      exact ⟨h, rfl⟩
    apply hli.notMem_span hy
    refine Submodule.span_mono ?_ hspan
    rintro _ ⟨h, rfl⟩
    refine ⟨AddMonoidAlgebra.single h 1, ⟨hgl1 h, ?_⟩, rfl⟩
    intro heq
    exact hne h (Set.mem_singleton_iff.mp heq).symm
  choose M hM using fun g => key _ (hgl g)
  refine ⟨⟨⟨M, ?_⟩, ?_⟩, hM⟩
  ·
    have h1 : f (AddMonoidAlgebra.single 0 1) = AddMonoidAlgebra.single 0 1 := by
      rw [show (AddMonoidAlgebra.single (0 : G) (1 : S)) = 1 from rfl, map_one]
    have := (hM 0).symm.trans h1
    exact (AddMonoidAlgebra.single_left_injective one_ne_zero this)
  ·
    intro g g'
    have hmul : f (AddMonoidAlgebra.single (g + g') 1) = f (AddMonoidAlgebra.single g 1) * f (AddMonoidAlgebra.single g' 1) := by
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
    rw [hM, hM, hM, AddMonoidAlgebra.single_mul_single, mul_one] at hmul
    exact AddMonoidAlgebra.single_left_injective one_ne_zero hmul


-- created on 2026-10-09
