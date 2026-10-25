import Mathlib
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2
import Abbrev.Analysis.Section_3_1_api
import Def.Analysis.Section_3_epilogue
set_option doc.verso.suggestions false
set_option backward.isDefEq.respectTransparency false

universe u

/-!
# Analysis I, Chapter 3 epilogue: Connections with ZFSet

In this epilogue we show that the {name}`ZFSet` type in Mathlib (derived as a quotient from the
{name}`PSet` type) can be used to create models of the `SetTheory` class studied in this chapter, so long as we work in a universe of level at
least 1.  The constructions here are due to Edward van de Meent; see
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Can.20this.20proof.20related.20to.20Set.20replacement.20be.20shorter.3F/near/527305173
-/


open Classical in
/-- Show that {name}`ZFSet` obeys the {name}`Chapter3.SetTheory` axioms.  Most of these axioms were
essentially already established in Mathlib and are relatively routine to transfer over;
the equivalence of `ZF.omega` and {name}`Nat` being the trickiest one in content (and the
power set axiom also requiring some technical manipulation). -/
noncomputable instance ZFSet.inst_SetTheory : Chapter3.SetTheory.{u + 1,u + 1} where
  Set := ZFSet
  Object := ZFSet
  set_to_object := { toFun ⦃a₁⦄ := a₁, inj' _ _ h := h}
  mem o s := o ∈ s
  extensionality _ _ := ext
  emptyset := ∅
  emptyset_mem := notMem_empty
  singleton x := {x}
  singleton_axiom _ _ := mem_singleton
  union_pair x y := x ∪ y
  union_pair_axiom _ _ _ := mem_union
  specify A P := ZFSet.sep (fun s ↦ (h : s ∈ A) → P ⟨s,h⟩) A
  specification_axiom := by simp +contextual
  replace A P hp := @(A.sep (fun s ↦ (hs : s ∈ A) → ∃ z, P ⟨s,hs⟩ z)).image (fun s ↦
    if h : ∃ (hs : s ∈ A), ∃ z, P ⟨s,hs⟩ z then h.choose_spec.choose else ∅) (allZFSetDefinable _)
  replacement_axiom A P hp s := by
    simp; constructor
    · intro ⟨z, ⟨hzA, hz⟩, hz'⟩; use z, hzA; simp [hzA, hz hzA] at hz'
      simp [←hz', Exists.choose_spec]
    · intro ⟨z, hzA, hz'⟩; use z, ⟨hzA, by aesop⟩
      apply hp ⟨_, hzA⟩; rw [dif_pos ⟨hzA, ⟨_, hz'⟩⟩]; use Exists.choose_spec _
  nat := omega
  nat_equiv := nat_equiv
  regularity_axiom A := by
    intro hA
    obtain ⟨x, hx⟩ := hA
    obtain ⟨y, hy, hinter⟩ := regularity A (by
      rintro rfl
      exact notMem_empty x hx)
    refine ⟨y, hy, ?_⟩
    intro S hS ⟨z, hzA, hzS⟩
    have hzS' : z ∈ y := by
      rw [hS]
      exact hzS
    have hz : z ∈ ZFSet.inter A y := (ZFSet.mem_sep).mpr ⟨hzA, hzS'⟩
    rw [show ZFSet.inter A y = ∅ from hinter] at hz
    exact notMem_empty z hz
  pow X Y := funs Y X
  function_to_object X Y := {
    toFun f := @map (fun s ↦ if h : s ∈ X then f ⟨s,h⟩ else ∅) (allZFSetDefinable _) X
    inj' x _ h := by
      ext ⟨s, hs⟩; simp_rw [ZFSet.ext_iff, mem_map] at h
      specialize h (s.pair (x ⟨_,hs⟩)); aesop}
  powerset_axiom X Y F := by
    rw [mem_funs]
    constructor
    · intro ⟨hsub, huniq⟩
      let g : Subtype (· ∈ Y) → Subtype (· ∈ X) := fun y ↦
        ⟨(huniq y.val y.property).choose,
          (pair_mem_prod.mp (hsub (huniq y.val y.property).choose_spec)).2⟩
      let φ : ZFSet → ZFSet := fun s ↦ if h : s ∈ Y then (g ⟨s, h⟩ : ZFSet) else ∅
      let hφ : Definable₁ φ := allZFSetDefinable _
      refine ⟨g, ?_⟩
      show @map φ hφ Y = F
      apply ZFSet.ext
      intro z
      constructor
      · intro hz
        rw [@mem_map φ hφ] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        have : φ y = (huniq y hy).choose := by simp [φ, g, hy]
        simpa [this] using (huniq y hy).choose_spec
      · intro hz
        have hzy := hsub hz
        rw [mem_prod] at hzy
        obtain ⟨y, hy, w, _, rfl⟩ := hzy
        rw [@mem_map φ hφ]
        refine ⟨y, hy, ?_⟩
        have hw' : (huniq y hy).choose = w := (huniq y hy).choose_eq hz
        have : φ y = w := by simp [φ, g, hy, hw']
        simpa [this]
    · rintro ⟨f, rfl⟩
      let φ : ZFSet → ZFSet := fun s ↦ if h : s ∈ Y then (f ⟨s, h⟩ : ZFSet) else ∅
      let hφ : Definable₁ φ := allZFSetDefinable _
      show IsFunc Y X (@map φ hφ Y)
      rw [map_isFunc]
      intro z hz
      simp [φ, hz]
  union := sUnion
  union_axiom A x := by
    rw [mem_sUnion]
    constructor
    · rintro ⟨S, hSA, hxS⟩
      exact ⟨S, hxS, hSA⟩
    · rintro ⟨S, hxS, hSA⟩
      exact ⟨S, hSA, hxS⟩

