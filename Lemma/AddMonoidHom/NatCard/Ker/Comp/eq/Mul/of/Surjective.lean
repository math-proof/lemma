import Mathlib
import sympy.Basic


/--
[AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective.lean)
-/

def kerMap
  {A B C : Type*}
  [AddGroup A]
  [AddGroup B]
  [AddGroup C]
  (f : A →+ B) (g : B →+ C) : (g.comp f).ker →+ g.ker :=
  (f.domRestrict (g.comp f).ker).codRestrict g.ker fun x => by
    rw [AddMonoidHom.domRestrict_apply, AddMonoidHom.mem_ker]
    have hx := x.2
    rwa [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply] at hx

@[simp] private lemma kerMap_apply
  {A B C : Type*}
  [AddGroup A]
  [AddGroup B]
  [AddGroup C]
  (f : A →+ B) (g : B →+ C) (x : (g.comp f).ker) :
  (kerMap f g x : B) = f x := rfl

private lemma  kerMap_surjective
  {A B C : Type*}
  [AddGroup A]
  [AddGroup B]
  [AddGroup C]
  (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
  Function.Surjective (kerMap f g) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨⟨x, ?_⟩, Subtype.ext rfl⟩
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
  rwa [AddMonoidHom.mem_ker] at hy

private lemma  ker_le
  {A B C : Type*}
  [AddGroup A]
  [AddGroup B]
  [AddGroup C]
  (f : A →+ B) (g : B →+ C) : f.ker ≤ (g.comp f).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx, map_zero]

private lemma  ker_kerMap
  {A B C : Type*}
  [AddGroup A]
  [AddGroup B]
  [AddGroup C]
  (f : A →+ B) (g : B →+ C) :
  (kerMap f g).ker = f.ker.addSubgroupOf (g.comp f).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker,
    ← kerMap_apply]
  exact ⟨fun h => by rw [h, AddSubgroup.coe_zero], fun h => Subtype.ext h⟩

private lemma  natCard_ker_comp
  {A B C : Type*}
  [AddGroup A]
  [AddGroup B]
  [AddGroup C]
  (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
  Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker :=
  calc _ = Nat.card ((g.comp f).ker ⧸ (kerMap f g).ker) * Nat.card (kerMap f g).ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card g.ker * Nat.card f.ker := by
        rw [Nat.card_congr
            (QuotientAddGroup.quotientKerEquivOfSurjective _ (kerMap_surjective f g hf)).toEquiv,
          ker_kerMap, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (ker_le f g)).toEquiv]

@[main]
private lemma main
  [AddGroup A] [AddGroup B] [AddGroup C]
  {f : A →+ B}
  {g : B →+ C}
-- given
  (hf : Function.Surjective f) :
-- imply
  Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker :=
-- proof
  natCard_ker_comp f g hf


-- created on 2026-10-09
