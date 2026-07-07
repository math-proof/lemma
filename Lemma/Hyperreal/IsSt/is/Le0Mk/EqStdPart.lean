import Lemma.Hyperreal.IsSt.is.All_LtAbs
import Lemma.Int.LtAbsSub.is.LtSub.Lt_Add
open Hyperreal Int


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*)
  (r : ℝ) :
-- imply
  (x - r) → 0 ↔ 0 ≤ ArchimedeanClass.mk x ∧ stdPart x = r := by
-- proof
  rw [IsSt.is.All_LtAbs]
  simp [LtAbsSub.is.LtSub.Lt_Add]
  constructor
  ·
    intro h
    refine ⟨?_, ArchimedeanClass.stdPart_eq Hyperreal.coeRingHom (fun s hs ↦ ?_) (fun s hs ↦ ?_)⟩
    ·
      have h := h 1 zero_lt_one
      exact ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean Hyperreal.coeRingHom h.1.le h.2.le
    ·
      simpa using (h _ (sub_pos_of_lt hs)).1.le
    ·
      simpa using (h _ (sub_pos_of_lt hs)).2.le
  ·
    intro h
    obtain ⟨h, rfl⟩ := h
    refine fun y hy ↦ ⟨?_, ?_⟩
    ·
      apply ArchimedeanClass.lt_of_lt_stdPart Hyperreal.coeRingHom h
      simpa
    ·
      apply ArchimedeanClass.lt_of_stdPart_lt Hyperreal.coeRingHom h
      simpa


-- created on 2026-07-07
