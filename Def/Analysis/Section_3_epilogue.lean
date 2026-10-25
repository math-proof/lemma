import Mathlib
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2
import Abbrev.Analysis.Section_3_1_api
import Theorem.Analysis.Section_3_epilogue
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


open PSet in
/-- Using the above lemmas, we can create a bijection between {name}`ZFSet.omega` and
the natural numbers. -/
noncomputable def ZFSet.nat_equiv : ℕ ≃ omega.{u} := Equiv.ofBijective (fun n => ⟨mk (ofNat.{u} n),mk_mem_iff.mpr (Mem.mk _ (ULift.up n))⟩) (by
  constructor
  · intro n m h
    apply eq_of_ofNat_equiv_ofNat
    exact (ZFSet.eq).mp (congrArg Subtype.val h)
  · intro ⟨x, hx⟩
    have hx' : x.out ∈ PSet.omega := by
      have hxmk : mk x.out ∈ omega := by rw [ZFSet.mk_out]; exact hx
      exact (ZFSet.mk_mem_iff).mp (by simpa [ZFSet.omega] using hxmk)
    obtain ⟨n, hn⟩ := hx'
    refine ⟨n.down, ?_⟩
    apply Subtype.ext
    show mk (ofNat n.down) = x
    rw [← ZFSet.mk_out x, ZFSet.eq]
    exact hn.symm
  )

