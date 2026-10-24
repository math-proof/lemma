import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section9
open CategoryTheory HomologyLongExactSequence FiveLemma FiveLemma.LongExactLadder
open FiveLemma


namespace FiveLemma

/--
[five_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma five_lemma
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {α₁ : A₁ →+ A₂}
  {α₂ : A₂ →+ A₃}
  {α₃ : A₃ →+ A₄}
  {α₄ : A₄ →+ A₅}
  {β₁ : B₁ →+ B₂}
  {β₂ : B₂ →+ B₃}
  {β₃ : B₃ →+ B₄}
  {β₄ : B₄ →+ B₅}
  {f₁ : A₁ →+ B₁}
  {f₂ : A₂ →+ B₂}
  {f₃ : A₃ →+ B₃}
  {f₄ : A₄ →+ B₄}
  {f₅ : A₅ →+ B₅}
-- given
  (hc₁ : β₁.comp f₁ = f₂.comp α₁)
  (hc₂ : β₂.comp f₂ = f₃.comp α₂)
  (hc₃ : β₃.comp f₃ = f₄.comp α₃)
  (hc₄ : β₄.comp f₄ = f₅.comp α₄)
  (hα₁ : Function.Exact α₁ α₂)
  (hα₂ : Function.Exact α₂ α₃)
  (hα₃ : Function.Exact α₃ α₄)
  (hβ₁ : Function.Exact β₁ β₂)
  (hβ₂ : Function.Exact β₂ β₃)
  (hβ₃ : Function.Exact β₃ β₄)
  (hf₁ : Function.Surjective f₁)
  (hf₂ : Function.Bijective f₂)
  (hf₄ : Function.Bijective f₄)
  (hf₅ : Function.Injective f₅) :
-- imply
  Function.Bijective f₃ :=
-- proof
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ f₁ f₂ f₃ f₄ f₅
    hc₁ hc₂ hc₃ hc₄ hα₁ hα₂ hα₃ hβ₁ hβ₂ hβ₃ hf₁ hf₂ hf₄ hf₅

end FiveLemma

namespace FiveLemma

/--
[HomologyLadder.h_bijective_of_f_g_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma HomologyLadder.h_bijective_of_f_g_bijective
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : HomologyLadder}
  {n : ℤ}
-- given
  (hf : ∀ n, Function.Bijective (L.fMap n))
  (hg : ∀ n, Function.Bijective (L.gMap n)) :
-- imply
  Function.Bijective (L.hMap (n + 1)) :=
-- proof
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.iMap (n + 1)) (L.pMap (n + 1)) (L.δ n) (L.iMap n)
    (L.iMap' (n + 1)) (L.pMap' (n + 1)) (L.δ' n) (L.iMap' n)
    (L.fMap (n + 1)) (L.gMap (n + 1)) (L.hMap (n + 1)) (L.fMap n) (L.gMap n)
    (L.comm_fi (n + 1)) (L.comm_gp (n + 1)) (L.comm_hδ n) (L.comm_fi n)
    (L.exact_ip (n + 1)) (L.exact_pδ n) (L.exact_δi n)
    (L.exact_i'p' (n + 1)) (L.exact_p'δ' n) (L.exact_δ'i' n)
    (hf (n + 1)).2 (hg (n + 1)) (hf n) (hg n).1

end FiveLemma

namespace FiveLemma

/--
[HomologyLadder.g_bijective_of_f_h_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma HomologyLadder.g_bijective_of_f_h_bijective
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : HomologyLadder}
  {n : ℤ}
-- given
  (hf : ∀ n, Function.Bijective (L.fMap n))
  (hh : ∀ n, Function.Bijective (L.hMap n)) :
-- imply
  Function.Bijective (L.gMap (n + 1)) :=
-- proof
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.δ (n + 1)) (L.iMap (n + 1)) (L.pMap (n + 1)) (L.δ n)
    (L.δ' (n + 1)) (L.iMap' (n + 1)) (L.pMap' (n + 1)) (L.δ' n)
    (L.hMap (n + 1 + 1)) (L.fMap (n + 1)) (L.gMap (n + 1)) (L.hMap (n + 1)) (L.fMap n)
    (L.comm_hδ (n + 1)) (L.comm_fi (n + 1)) (L.comm_gp (n + 1)) (L.comm_hδ n)
    (L.exact_δi (n + 1)) (L.exact_ip (n + 1)) (L.exact_pδ n)
    (L.exact_δ'i' (n + 1)) (L.exact_i'p' (n + 1)) (L.exact_p'δ' n)
    (hh (n + 1 + 1)).2 (hf (n + 1)) (hh (n + 1)) (hf n).1

end FiveLemma

namespace FiveLemma

/--
[HomologyLadder.f_bijective_of_g_h_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma HomologyLadder.f_bijective_of_g_h_bijective
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : HomologyLadder}
  {n : ℤ}
-- given
  (hg : ∀ n, Function.Bijective (L.gMap n))
  (hh : ∀ n, Function.Bijective (L.hMap n)) :
-- imply
  Function.Bijective (L.fMap n) :=
-- proof
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.pMap (n + 1)) (L.δ n) (L.iMap n) (L.pMap n)
    (L.pMap' (n + 1)) (L.δ' n) (L.iMap' n) (L.pMap' n)
    (L.gMap (n + 1)) (L.hMap (n + 1)) (L.fMap n) (L.gMap n) (L.hMap n)
    (L.comm_gp (n + 1)) (L.comm_hδ n) (L.comm_fi n) (L.comm_gp n)
    (L.exact_pδ n) (L.exact_δi n) (L.exact_ip n)
    (L.exact_p'δ' n) (L.exact_δ'i' n) (L.exact_i'p' n)
    (hg (n + 1)).2 (hh (n + 1)) (hg n) (hh n).1

end FiveLemma

namespace FiveLemma.LongExactLadder

/--
[two_of_three_fC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma two_of_three_fC
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : LongExactLadder}
  {n : ℤ}
-- given
  (hfA : ∀ n, Function.Bijective (L.fA n))
  (hfB : ∀ n, Function.Bijective (L.fB n)) :
-- imply
  Function.Bijective (L.fC n) := by
-- proof
  have h : n = (n - 1) + 1 := by omega
  rwa [h]
    (L.ι (n - 1 + 1)) (L.π (n - 1 + 1)) (L.δ (n - 1)) (L.ι (n - 1))
    (L.ι' (n - 1 + 1)) (L.π' (n - 1 + 1)) (L.δ' (n - 1)) (L.ι' (n - 1))
    (L.fA (n - 1 + 1)) (L.fB (n - 1 + 1)) (L.fC (n - 1 + 1)) (L.fA (n - 1)) (L.fB (n - 1))
    (L.comm_ι (n - 1 + 1)) (L.comm_π (n - 1 + 1)) (L.comm_δ (n - 1)) (L.comm_ι (n - 1))
    (L.exact_ιπ (n - 1 + 1)) (L.exact_πδ (n - 1)) (L.exact_δι (n - 1))
    (L.exact_ι'π' (n - 1 + 1)) (L.exact_π'δ' (n - 1)) (L.exact_δ'ι' (n - 1))
    (hfA (n - 1 + 1)).2 (hfB (n - 1 + 1)) (hfA (n - 1)) (hfB (n - 1)).1

end FiveLemma.LongExactLadder

namespace FiveLemma.LongExactLadder

/--
[two_of_three_fB_inj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma two_of_three_fB_inj
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : LongExactLadder}
  {n : ℤ}
-- given
  (hfA : ∀ n, Function.Bijective (L.fA n))
  (hfC : ∀ n, Function.Bijective (L.fC n)) :
-- imply
  Function.Injective (L.fB n) :=
-- proof
  AddMonoidHom.injective_of_surjective_of_injective_of_injective
    (L.δ n) (L.ι n) (L.π n)
    (L.δ' n) (L.ι' n) (L.π' n)
    (L.fC (n + 1)) (L.fA n) (L.fB n) (L.fC n)
    (L.comm_δ n) (L.comm_ι n) (L.comm_π n)
    (L.exact_δι n) (L.exact_ιπ n)
    (L.exact_δ'ι' n)
    (hfC (n + 1)).2 (hfA n).1 (hfC n).1

end FiveLemma.LongExactLadder

namespace FiveLemma.LongExactLadder

/--
[two_of_three_fB_surj_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma two_of_three_fB_surj_aux
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : LongExactLadder}
  {n : ℤ}
-- given
  (hfA : ∀ n, Function.Bijective (L.fA n))
  (hfC : ∀ n, Function.Bijective (L.fC n)) :
-- imply
  Function.Surjective (L.fB (n + 1)) :=
-- proof
  AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (L.ι (n + 1)) (L.π (n + 1)) (L.δ n)
    (L.ι' (n + 1)) (L.π' (n + 1)) (L.δ' n)
    (L.fA (n + 1)) (L.fB (n + 1)) (L.fC (n + 1)) (L.fA n)
    (L.comm_ι (n + 1)) (L.comm_π (n + 1)) (L.comm_δ n)
    (L.exact_πδ n) (L.exact_ι'π' (n + 1)) (L.exact_π'δ' n)
    (hfA (n + 1)).2 (hfC (n + 1)).2 (hfA n).1

end FiveLemma.LongExactLadder

namespace FiveLemma.LongExactLadder

/--
[two_of_three_fB](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma two_of_three_fB
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : LongExactLadder}
  {n : ℤ}
-- given
  (hfA : ∀ n, Function.Bijective (L.fA n))
  (hfC : ∀ n, Function.Bijective (L.fC n)) :
-- imply
  Function.Bijective (L.fB n) := by
-- proof
  refine ⟨two_of_three_fB_inj L hfA hfC n, ?_⟩
  have h : n = (n - 1) + 1 := by omega
  rw [h]
  exact two_of_three_fB_surj_aux L hfA hfC (n - 1)

end FiveLemma.LongExactLadder

namespace FiveLemma.LongExactLadder

/--
[two_of_three_fA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma two_of_three_fA
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : LongExactLadder}
  {n : ℤ}
-- given
  (hfB : ∀ n, Function.Bijective (L.fB n))
  (hfC : ∀ n, Function.Bijective (L.fC n)) :
-- imply
  Function.Bijective (L.fA n) :=
-- proof
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.π (n + 1)) (L.δ n) (L.ι n) (L.π n)
    (L.π' (n + 1)) (L.δ' n) (L.ι' n) (L.π' n)
    (L.fB (n + 1)) (L.fC (n + 1)) (L.fA n) (L.fB n) (L.fC n)
    (L.comm_π (n + 1)) (L.comm_δ n) (L.comm_ι n) (L.comm_π n)
    (L.exact_πδ n) (L.exact_δι n) (L.exact_ιπ n)
    (L.exact_π'δ' n) (L.exact_δ'ι' n) (L.exact_ι'π' n)
    (hfB (n + 1)).2 (hfC (n + 1)) (hfB n) (hfC n).1

end FiveLemma.LongExactLadder

namespace FiveLemma.LongExactLadder

/--
[two_of_three_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma two_of_three_iso
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : LongExactLadder}
-- given
  (h : (∀ n, Function.Bijective (L.fA n)) ∧ (∀ n, Function.Bijective (L.fB n)) ∨ (∀ n, Function.Bijective (L.fA n)) ∧ (∀ n, Function.Bijective (L.fC n)) ∨ (∀ n, Function.Bijective (L.fB n)) ∧ (∀ n, Function.Bijective (L.fC n))) :
-- imply
  (∀ n, Function.Bijective (L.fA n)) ∧ (∀ n, Function.Bijective (L.fB n)) ∧ (∀ n, Function.Bijective (L.fC n)) := by
-- proof
  obtain ⟨hA, hB⟩ | ⟨hA, hC⟩ | ⟨hB, hC⟩ := h
  · exact ⟨hA, hB, fun n => two_of_three_fC L hA hB n⟩
  · exact ⟨hA, fun n => two_of_three_fB L hA hC n, hC⟩
  · exact ⟨fun n => two_of_three_fA L hB hC n, hB, hC⟩

end FiveLemma.LongExactLadder

namespace FiveLemma

/--
[HomologyLadder.two_of_three_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
lemma HomologyLadder.two_of_three_bijective
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup B₁]
  [AddCommGroup B₂]
  [AddCommGroup B₃]
  {L : HomologyLadder} :
-- imply
  ((∀ n, Function.Bijective (L.fMap n)) → (∀ n, Function.Bijective (L.gMap n)) → ∀ n, Function.Bijective (L.hMap n)) ∧ ((∀ n, Function.Bijective (L.fMap n)) → (∀ n, Function.Bijective (L.hMap n)) → ∀ n, Function.Bijective (L.gMap n)) ∧ ((∀ n, Function.Bijective (L.gMap n)) → (∀ n, Function.Bijective (L.hMap n)) → ∀ n, Function.Bijective (L.fMap n)) :=
-- proof
  ⟨fun hf hg n => by
    have := L.h_bijective_of_f_g_bijective hf hg (n - 1)
    rwa [Int.sub_add_cancel] at this,
    fun hf hh n => by
      have := L.g_bijective_of_f_h_bijective hf hh (n - 1)
      rwa [Int.sub_add_cancel] at this,
    fun hg hh n => L.f_bijective_of_g_h_bijective hg hh n⟩
end FiveLemma
namespace EilenbergSteenrod
open FiveLemma


/--
[exact_f_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
private lemma exact_f_g_eq
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {i : ι}
-- given
  (hS : S.ShortExact) :
-- imply
  (ShortComplex.mk (HomologicalComplex.homologyMap S.f i) (HomologicalComplex.homologyMap S.g i) (by rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])).Exact := by
-- proof
  apply HomologyLongExactSequence.exact_f_g hS i

/--
[exact_g_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
private lemma exact_g__eq
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact := by
-- proof
  apply HomologyLongExactSequence.exact_g_ hS i j hij

/--
[exact_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean)
-/
@[path]
private lemma exact__eq
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact := by
-- proof
  apply HomologyLongExactSequence.exact_ hS i j hij


-- created on 2026-10-23
