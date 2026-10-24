import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PeakStatistic231
open MetaMathlibExt


namespace MetaMathlibExt.Peak231

/--
[joinMax_apply_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_apply_lt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  {i : Fin (a + b + 1)} (h : i.val < a) :
  (joinMax α β i).val = (α ⟨i.val, h⟩).val := by
  simp only [joinMax, Equiv.ofBijective_apply, joinMaxFun, dite_eq_left h]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_apply_eq {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
  joinMax α β ⟨a, by omega⟩ = Fin.last (a + b) := by
  have hneg : ¬ (⟨a, by omega⟩ : Fin (a + b + 1)).val < a := by
    change ¬ a < a
    exact lt_irrefl _
  simp only [joinMax, Equiv.ofBijective_apply, joinMaxFun]
  rw [dite_eq_right hneg]
  simp

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_apply_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_apply_gt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  {i : Fin (a + b + 1)} (h : a < i.val) :
  (joinMax α β i).val = a + (β ⟨i.val - a - 1, by omega⟩).val := by
  simp only [joinMax, Equiv.ofBijective_apply, joinMaxFun,
    dite_eq_right (by omega : ¬ i.val < a), dite_eq_right (by omega : ¬ i.val = a)]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_symm_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_symm_last {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
  (joinMax α β).symm (Fin.last (a + b)) = ⟨a, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  exact (joinMax_apply_eq α β).symm

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_inj {a b : ℕ} {α α' : Equiv.Perm (Fin a)} {β β' : Equiv.Perm (Fin b)}
  (h : joinMax α β = joinMax α' β') : α = α' ∧ β = β' := by
  have hα : α = α' := by
    apply Equiv.ext
    intro j
    set pos : Fin (a + b + 1) := ⟨j.val, by have hj := j.isLt; omega⟩ with hpos_def
    have hpos : pos.val < a := j.isLt
    have h2 := congrArg (fun e : Equiv.Perm (Fin (a + b + 1)) => e pos) h
    have h2v := congrArg Fin.val h2
    have e1 := joinMax_apply_lt α β (i := pos) hpos
    have e2 := joinMax_apply_lt α' β' (i := pos) hpos
    rw [e1, e2] at h2v
    have e : (⟨pos.val, hpos⟩ : Fin a) = j := by
      apply Fin.ext
      change pos.val = j.val
      rw [hpos_def]
    rw [e] at h2v
    exact Fin.ext h2v
  have hβ : β = β' := by
    apply Equiv.ext
    intro j
    set pos : Fin (a + b + 1) := ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩ with hpos_def
    have hpos : a < pos.val := by
      change a < a + 1 + j.val
      omega
    have h2 := congrArg (fun e : Equiv.Perm (Fin (a + b + 1)) => e pos) h
    have h2v := congrArg Fin.val h2
    have e1 := joinMax_apply_gt α β (i := pos) hpos
    have e2 := joinMax_apply_gt α' β' (i := pos) hpos
    rw [e1, e2] at h2v
    have hsub : pos.val - a - 1 = j.val := by
      have : pos.val = a + 1 + j.val := by rw [hpos_def]
      omega
    -- canonical re-ascription (proof irrelevance makes this defeq to h2v)
    have h2c : (β ⟨pos.val - a - 1, by have hj := j.isLt; omega⟩).val =
      (β' ⟨pos.val - a - 1, by have hj := j.isLt; omega⟩).val :=
      add_left_cancel_iff.mp (by exact h2v)
    have eB : (⟨pos.val - a - 1, by have hj := j.isLt; omega⟩ : Fin b) = j := by
      apply Fin.ext
      change pos.val - a - 1 = j.val
      exact hsub
    rw [eB] at h2c
    exact Fin.ext h2c
  exact ⟨hα, hβ⟩

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_val_lt_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_val_lt_of_lt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  {p : Fin (a + b + 1)} (h : p.val < a) : (joinMax α β p).val < a := by
  rw [joinMax_apply_lt α β h]
  exact (α ⟨p.val, h⟩).isLt

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_ge_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_ge_of_gt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  {p : Fin (a + b + 1)} (h : a < p.val) : a ≤ (joinMax α β p).val := by
  rw [joinMax_apply_gt α β h]
  omega

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_val_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_val_of_eq {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  {p : Fin (a + b + 1)} (h : p.val = a) : (joinMax α β p).val = a + b := by
  have hp : p = ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩ := Fin.ext h
  rw [hp]
  exact congrArg Fin.val (joinMax_apply_eq α β)

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_pos_lt_of_val_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_pos_lt_of_val_lt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  (p : Fin (a + b + 1)) (h : (joinMax α β p).val < a) : p.val < a := by
  obtain hlt | hge := lt_or_ge p.val a
  · exact hlt
  · exfalso
    obtain he | hgt := eq_or_lt_of_le hge
    · have hv : (joinMax α β p).val = a + b := joinMax_val_of_eq α β he.symm
      omega
    · have hv : a ≤ (joinMax α β p).val := joinMax_ge_of_gt α β hgt
      omega

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_val_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_val_left {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  (x : Fin a) : (joinMax α β ⟨x.val, by have hx := x.isLt; omega⟩).val = (α x).val := by
  have h : (⟨x.val, by have hx := x.isLt; omega⟩ : Fin (a + b + 1)).val < a := x.isLt
  exact joinMax_apply_lt α β h

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_val_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_val_right {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  (y : Fin b) :
  (joinMax α β ⟨a + 1 + y.val, by have hy := y.isLt; omega⟩).val = a + (β y).val := by
  have h : a < (⟨a + 1 + y.val, by have hy := y.isLt; omega⟩ : Fin (a + b + 1)).val := by
    change a < a + 1 + y.val
    omega
  have e := joinMax_apply_gt α β h
  have hU : (⟨(⟨a + 1 + y.val, by have hy := y.isLt; omega⟩ : Fin (a + b + 1)).val - a - 1,
    by have hy := y.isLt; omega⟩ : Fin b) = y := by
    apply Fin.ext
    change a + 1 + y.val - a - 1 = y.val
    omega
  conv_rhs => rw [← hU]
  exact e

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[avoids231_joinMax_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma avoids231_joinMax_iff {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
  Avoids231 (joinMax α β) ↔ Avoids231 α ∧ Avoids231 β := by
  constructor
  · intro hAv
    refine ⟨?_, ?_⟩
    · intro i j l hij hjl h231
      obtain ⟨h1, h2⟩ := h231
      have hvij : i.val < j.val := Fin.lt_def.mp hij
      have hvjl : j.val < l.val := Fin.lt_def.mp hjl
      have h1v : (α l).val < (α i).val := Fin.lt_def.mp h1
      have h2v : (α i).val < (α j).val := Fin.lt_def.mp h2
      set I : Fin (a + b + 1) := ⟨i.val, by have hi := i.isLt; omega⟩ with hIdef
      set J : Fin (a + b + 1) := ⟨j.val, by have hj := j.isLt; omega⟩ with hJdef
      set L : Fin (a + b + 1) := ⟨l.val, by have hl := l.isLt; omega⟩ with hLdef
      have oIJ : I < J := Fin.lt_def.mpr (by
        have eI : I.val = i.val := by rw [hIdef]
        have eJ : J.val = j.val := by rw [hJdef]
        omega)
      have oJL : J < L := Fin.lt_def.mpr (by
        have eJ : J.val = j.val := by rw [hJdef]
        have eL : L.val = l.val := by rw [hLdef]
        omega)
      have vI : ((joinMax α β) I).val = (α i).val := joinMax_val_left α β i
      have vJ : ((joinMax α β) J).val = (α j).val := joinMax_val_left α β j
      have vL : ((joinMax α β) L).val = (α l).val := joinMax_val_left α β l
      have g1 : (joinMax α β) L < (joinMax α β) I := Fin.lt_def.mpr (by omega)
      have g2 : (joinMax α β) I < (joinMax α β) J := Fin.lt_def.mpr (by omega)
      exact hAv I J L oIJ oJL ⟨g1, g2⟩
    · intro i j l hij hjl h231
      obtain ⟨h1, h2⟩ := h231
      have hvij : i.val < j.val := Fin.lt_def.mp hij
      have hvjl : j.val < l.val := Fin.lt_def.mp hjl
      have h1v : (β l).val < (β i).val := Fin.lt_def.mp h1
      have h2v : (β i).val < (β j).val := Fin.lt_def.mp h2
      set I : Fin (a + b + 1) := ⟨a + 1 + i.val, by have hi := i.isLt; omega⟩ with hIdef
      set J : Fin (a + b + 1) := ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩ with hJdef
      set L : Fin (a + b + 1) := ⟨a + 1 + l.val, by have hl := l.isLt; omega⟩ with hLdef
      have oIJ : I < J := Fin.lt_def.mpr (by
        have eI : I.val = a + 1 + i.val := by rw [hIdef]
        have eJ : J.val = a + 1 + j.val := by rw [hJdef]
        omega)
      have oJL : J < L := Fin.lt_def.mpr (by
        have eJ : J.val = a + 1 + j.val := by rw [hJdef]
        have eL : L.val = a + 1 + l.val := by rw [hLdef]
        omega)
      have vI : ((joinMax α β) I).val = a + (β i).val := joinMax_val_right α β i
      have vJ : ((joinMax α β) J).val = a + (β j).val := joinMax_val_right α β j
      have vL : ((joinMax α β) L).val = a + (β l).val := joinMax_val_right α β l
      have g1 : (joinMax α β) L < (joinMax α β) I := Fin.lt_def.mpr (by omega)
      have g2 : (joinMax α β) I < (joinMax α β) J := Fin.lt_def.mpr (by omega)
      exact hAv I J L oIJ oJL ⟨g1, g2⟩
  · intro hAB i j l hij hjl h231
    obtain ⟨hα, hβ⟩ := hAB
    obtain ⟨h1, h2⟩ := h231
    have v1 : ((joinMax α β) l).val < ((joinMax α β) i).val := Fin.lt_def.mp h1
    have v2 : ((joinMax α β) i).val < ((joinMax α β) j).val := Fin.lt_def.mp h2
    have hvij : i.val < j.val := Fin.lt_def.mp hij
    have hvjl : j.val < l.val := Fin.lt_def.mp hjl
    obtain hiA | hiA := lt_or_ge i.val a
    · have hva : ((joinMax α β) i).val < a := joinMax_val_lt_of_lt α β hiA
      have hla : l.val < a := by
        have hlt : ((joinMax α β) l).val < a := by omega
        exact joinMax_pos_lt_of_val_lt α β l hlt
      have hja : j.val < a := by omega
      set I : Fin a := ⟨i.val, hiA⟩ with hIdef
      set J : Fin a := ⟨j.val, hja⟩ with hJdef
      set L : Fin a := ⟨l.val, hla⟩ with hLdef
      have oIJ : I < J := Fin.lt_def.mpr (by
        have eI : I.val = i.val := by rw [hIdef]
        have eJ : J.val = j.val := by rw [hJdef]
        omega)
      have oJL : J < L := Fin.lt_def.mpr (by
        have eJ : J.val = j.val := by rw [hJdef]
        have eL : L.val = l.val := by rw [hLdef]
        omega)
      have wI : (α I).val = ((joinMax α β) i).val := (joinMax_val_left α β I).symm
      have wJ : (α J).val = ((joinMax α β) j).val := (joinMax_val_left α β J).symm
      have wL : (α L).val = ((joinMax α β) l).val := (joinMax_val_left α β L).symm
      have g1 : α L < α I := Fin.lt_def.mpr (by omega)
      have g2 : α I < α J := Fin.lt_def.mpr (by omega)
      exact hα I J L oIJ oJL ⟨g1, g2⟩
    · rcases eq_or_lt_of_le hiA with he | hgt
      · have hv : ((joinMax α β) i).val = a + b := joinMax_val_of_eq α β he.symm
        have hjb : ((joinMax α β) j).val < a + b + 1 := (joinMax α β j).isLt
        omega
      · have hja : a < j.val := by omega
        have hla : a < l.val := by omega
        set I : Fin b := ⟨i.val - a - 1, by have hii := i.isLt; omega⟩ with hIdef
        set J : Fin b := ⟨j.val - a - 1, by have hjj := j.isLt; omega⟩ with hJdef
        set L : Fin b := ⟨l.val - a - 1, by have hll := l.isLt; omega⟩ with hLdef
        have oIJ : I < J := Fin.lt_def.mpr (by
          have eI : I.val = i.val - a - 1 := by rw [hIdef]
          have eJ : J.val = j.val - a - 1 := by rw [hJdef]
          omega)
        have oJL : J < L := Fin.lt_def.mpr (by
          have eJ : J.val = j.val - a - 1 := by rw [hJdef]
          have eL : L.val = l.val - a - 1 := by rw [hLdef]
          omega)
        have hIlt : a < i.val := hgt
        have hJlt : a < j.val := hja
        have hLlt : a < l.val := hla
        have eI := joinMax_apply_gt α β (i := i) hIlt
        have eJ := joinMax_apply_gt α β (i := j) hJlt
        have eL := joinMax_apply_gt α β (i := l) hLlt
        have wI : ((joinMax α β) i).val = a + (β I).val := eI
        have wJ : ((joinMax α β) j).val = a + (β J).val := eJ
        have wL : ((joinMax α β) l).val = a + (β L).val := eL
        have g1 : β L < β I := Fin.lt_def.mpr (by omega)
        have g2 : β I < β J := Fin.lt_def.mpr (by omega)
        exact hβ I J L oIJ oJL ⟨g1, g2⟩

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[joinMax_val_gt_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma joinMax_val_gt_of {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  {p : Fin (a + b + 1)} (h : a < p.val) (y : Fin b) (hy : y.val = p.val - a - 1) :
  ((joinMax α β) p).val = a + (β y).val := by
  have e := joinMax_apply_gt α β (i := p) h
  have hh : (⟨p.val - a - 1, by have hii := p.isLt; omega⟩ : Fin b) = y := by
    apply Fin.ext
    change p.val - a - 1 = y.val
    omega
  rw [e, hh]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[isPeakAt_joinMax_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma isPeakAt_joinMax_left {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  (i : ℕ) (h : i < a) :
  IsPeakAt (joinMax α β) ⟨i, by omega⟩ ↔ IsPeakAt α ⟨i, h⟩ := by
  set I : Fin (a + b + 1) := ⟨i, by omega⟩ with hIdef
  change IsPeakAt (joinMax α β) I ↔ IsPeakAt α ⟨i, h⟩
  have eI : I.val = i := by rw [hIdef]
  have hIa : I.val < a := h
  constructor
  · rintro ⟨pPrev, pNext, h1, h2, g1, g2⟩
    have h1' : pPrev.val + 1 = i := h1
    have h2' : i + 1 = pNext.val := h2
    have hva : ((joinMax α β) I).val < a := joinMax_val_lt_of_lt α β hIa
    have g1v : ((joinMax α β) pPrev).val < ((joinMax α β) I).val := Fin.lt_def.mp g1
    have g2v : ((joinMax α β) pNext).val < ((joinMax α β) I).val := Fin.lt_def.mp g2
    obtain hnA | hnA := lt_or_ge pNext.val a
    · have hpA : pPrev.val < a := by omega
      set qPrev : Fin a := ⟨pPrev.val, hpA⟩ with hqPdef
      set qNext : Fin a := ⟨pNext.val, hnA⟩ with hqNdef
      have eP : qPrev.val = pPrev.val := by rw [hqPdef]
      have eN : qNext.val = pNext.val := by rw [hqNdef]
      have wP : (α qPrev).val = ((joinMax α β) pPrev).val :=
        (joinMax_val_left α β qPrev).symm
      have wN : (α qNext).val = ((joinMax α β) pNext).val :=
        (joinMax_val_left α β qNext).symm
      have wI : (α ⟨i, h⟩).val = ((joinMax α β) I).val :=
        (joinMax_val_left α β ⟨i, h⟩).symm
      refine ⟨qPrev, qNext, ?_, ?_, ?_, ?_⟩
      · show qPrev.val + 1 = (⟨i, h⟩ : Fin a).val
        omega
      · show (⟨i, h⟩ : Fin a).val + 1 = qNext.val
        omega
      · exact Fin.lt_def.mpr (by omega)
      · exact Fin.lt_def.mpr (by omega)
    · have heq : pNext.val = a := by omega
      have hv : ((joinMax α β) pNext).val = a + b := joinMax_val_of_eq α β heq
      omega
  · rintro ⟨qPrev, qNext, h1, h2, g1, g2⟩
    have h1' : qPrev.val + 1 = i := h1
    have h2' : i + 1 = qNext.val := h2
    have g1v : (α qPrev).val < (α ⟨i, h⟩).val := Fin.lt_def.mp g1
    have g2v : (α qNext).val < (α ⟨i, h⟩).val := Fin.lt_def.mp g2
    set P : Fin (a + b + 1) := ⟨qPrev.val, by have hq := qPrev.isLt; omega⟩ with hPdef
    set Q : Fin (a + b + 1) := ⟨qNext.val, by have hq := qNext.isLt; omega⟩ with hQdef
    have eP : P.val = qPrev.val := by rw [hPdef]
    have eQ : Q.val = qNext.val := by rw [hQdef]
    have wP : ((joinMax α β) P).val = (α qPrev).val := joinMax_val_left α β qPrev
    have wQ : ((joinMax α β) Q).val = (α qNext).val := joinMax_val_left α β qNext
    have wI : ((joinMax α β) I).val = (α ⟨i, h⟩).val := joinMax_val_left α β ⟨i, h⟩
    refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
    · show P.val + 1 = I.val
      omega
    · show I.val + 1 = Q.val
      omega
    · exact Fin.lt_def.mpr (by omega)
    · exact Fin.lt_def.mpr (by omega)

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[isPeakAt_joinMax_mid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma isPeakAt_joinMax_mid {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
  IsPeakAt (joinMax α β) ⟨a, by omega⟩ ↔ ¬ (a = 0 ∨ b = 0) := by
  set M : Fin (a + b + 1) := ⟨a, by omega⟩ with hMdef
  change IsPeakAt (joinMax α β) M ↔ ¬ (a = 0 ∨ b = 0)
  have eM : M.val = a := by rw [hMdef]
  constructor
  · rintro ⟨pPrev, pNext, h1, h2, _, _⟩
    intro hcon
    obtain rfl | rfl := hcon
    · omega
    · have hPlt : pNext.val < a + 0 + 1 := pNext.isLt
      omega
  · intro hne
    have ha : a ≠ 0 := fun hz => hne (Or.inl hz)
    have hb : b ≠ 0 := fun hz => hne (Or.inr hz)
    set P : Fin (a + b + 1) := ⟨a - 1, by omega⟩ with hPdef
    set Q : Fin (a + b + 1) := ⟨a + 1, by omega⟩ with hQdef
    have eP : P.val = a - 1 := by rw [hPdef]
    have eQ : Q.val = a + 1 := by rw [hQdef]
    have hMlast : joinMax α β M = Fin.last (a + b) := joinMax_apply_eq α β
    have g1 : (joinMax α β) P < (joinMax α β) M := by
      rw [hMlast, Fin.lt_last_iff_ne_last]
      intro hcon
      have hPM : P = M := by
        apply (joinMax α β).injective
        rwa [hMlast]
      have hval := congrArg Fin.val hPM
      omega
    have g2 : (joinMax α β) Q < (joinMax α β) M := by
      rw [hMlast, Fin.lt_last_iff_ne_last]
      intro hcon
      have hQM : Q = M := by
        apply (joinMax α β).injective
        rwa [hMlast]
      have hval := congrArg Fin.val hQM
      omega
    refine ⟨P, Q, ?_, ?_, g1, g2⟩
    · show P.val + 1 = M.val
      omega
    · show M.val + 1 = Q.val
      omega

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[isPeakAt_joinMax_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma isPeakAt_joinMax_right {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
  (j : ℕ) (h : j < b) :
  IsPeakAt (joinMax α β) ⟨a + 1 + j, by omega⟩ ↔ IsPeakAt β ⟨j, h⟩ := by
  set R : Fin (a + b + 1) := ⟨a + 1 + j, by omega⟩ with hRdef
  change IsPeakAt (joinMax α β) R ↔ IsPeakAt β ⟨j, h⟩
  have eR : R.val = a + 1 + j := by rw [hRdef]
  have hRa : a < R.val := by omega
  constructor
  · rintro ⟨pPrev, pNext, h1, h2, g1, g2⟩
    have h1' : pPrev.val + 1 = a + 1 + j := by omega
    have h2' : a + 1 + j + 1 = pNext.val := by omega
    have g1v : ((joinMax α β) pPrev).val < ((joinMax α β) R).val := Fin.lt_def.mp g1
    have g2v : ((joinMax α β) pNext).val < ((joinMax α β) R).val := Fin.lt_def.mp g2
    have hRtop : ((joinMax α β) R).val < a + b + 1 := (joinMax α β R).isLt
    obtain hpA | hpA := lt_or_ge a pPrev.val
    · have hnA : pNext.val < a + b + 1 := pNext.isLt
      have hpB : pPrev.val - a - 1 < b := by omega
      have hnB : pNext.val - a - 1 < b := by omega
      obtain ⟨qPrev, eP⟩ : ∃ q : Fin b, q.val = pPrev.val - a - 1 :=
        ⟨⟨pPrev.val - a - 1, hpB⟩, rfl⟩
      obtain ⟨qNext, eN⟩ : ∃ q : Fin b, q.val = pNext.val - a - 1 :=
        ⟨⟨pNext.val - a - 1, hnB⟩, rfl⟩
      have hplt : a < pNext.val := by omega
      have wP : ((joinMax α β) pPrev).val = a + (β qPrev).val :=
        joinMax_val_gt_of α β hpA qPrev eP
      have wN : ((joinMax α β) pNext).val = a + (β qNext).val :=
        joinMax_val_gt_of α β hplt qNext eN
      have wR : ((joinMax α β) R).val = a + (β ⟨j, h⟩).val := joinMax_val_right α β ⟨j, h⟩
      refine ⟨qPrev, qNext, ?_, ?_, ?_, ?_⟩
      · change qPrev.val + 1 = j
        omega
      · change j + 1 = qNext.val
        omega
      · exact Fin.lt_def.mpr (by omega)
      · exact Fin.lt_def.mpr (by omega)
    · have heq : pPrev.val = a := by omega
      have hv : ((joinMax α β) pPrev).val = a + b := joinMax_val_of_eq α β heq
      omega
  · rintro ⟨qPrev, qNext, h1, h2, g1, g2⟩
    have h1' : qPrev.val + 1 = j := h1
    have h2' : j + 1 = qNext.val := h2
    have g1v : (β qPrev).val < (β ⟨j, h⟩).val := Fin.lt_def.mp g1
    have g2v : (β qNext).val < (β ⟨j, h⟩).val := Fin.lt_def.mp g2
    set P : Fin (a + b + 1) := ⟨a + 1 + qPrev.val, by have hq := qPrev.isLt; omega⟩ with hPdef
    set Q : Fin (a + b + 1) := ⟨a + 1 + qNext.val, by have hq := qNext.isLt; omega⟩ with hQdef
    have eP : P.val = a + 1 + qPrev.val := by rw [hPdef]
    have eQ : Q.val = a + 1 + qNext.val := by rw [hQdef]
    have hPgt : a < P.val := by omega
    have hQgt : a < Q.val := by omega
    have wP : ((joinMax α β) P).val = a + (β qPrev).val :=
      joinMax_val_gt_of α β hPgt qPrev (by omega)
    have wQ : ((joinMax α β) Q).val = a + (β qNext).val :=
      joinMax_val_gt_of α β hQgt qNext (by omega)
    have wR : ((joinMax α β) R).val = a + (β ⟨j, h⟩).val := joinMax_val_right α β ⟨j, h⟩
    refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
    · show P.val + 1 = R.val
      omega
    · show R.val + 1 = Q.val
      omega
    · exact Fin.lt_def.mpr (by omega)
    · exact Fin.lt_def.mpr (by omega)

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[peakCount_joinMax](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma peakCount_joinMax {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
  peakCount (joinMax α β) = peakCount α + peakCount β + (if a = 0 ∨ b = 0 then 0 else 1) := by
  have hcard : ∀ {m : ℕ} (σ : Equiv.Perm (Fin m)),
    peakCount σ = ∑ i ∈ Finset.range m,
      (if h : i < m then (if IsPeakAt σ ⟨i, h⟩ then (1:ℕ) else 0) else 0) := by
    intro m σ
    unfold peakCount
    rw [Finset.card_filter, Finset.sum_fin_eq_sum_range]
  simp only [hcard]
  have hrange : Finset.range (a + b + 1) = Finset.range (a + (b + 1)) := by
    have heq : a + b + 1 = a + (b + 1) := by omega
    rw [heq]
  rw [hrange, Finset.sum_range_add _ a (b + 1), Finset.sum_range_succ' _ b]
  have e1 : (∑ x ∈ Finset.range a,
    (if h : x < a + b + 1 then
      (if IsPeakAt (joinMax α β) ⟨x, h⟩ then (1 : ℕ) else 0) else 0)) =
    ∑ x ∈ Finset.range a,
    (if h : x < a then (if IsPeakAt α ⟨x, h⟩ then (1 : ℕ) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hii : i < a := Finset.mem_range.mp hi
    have hbound : i < a + b + 1 := by omega
    rw [dite_eq_left hbound, dite_eq_left hii]
    have key := isPeakAt_joinMax_left α β i hii
    by_cases hpk : IsPeakAt α ⟨i, hii⟩
    · have h1 : IsPeakAt (joinMax α β) ⟨i, hbound⟩ := key.mpr hpk
      simp only [h1, hpk, ite_true]
    · have h1 : ¬ IsPeakAt (joinMax α β) ⟨i, hbound⟩ := fun h => hpk (key.mp h)
      simp only [h1, hpk, ite_false]
  have e2 : (∑ k ∈ Finset.range b,
    (if h : a + (k + 1) < a + b + 1 then
      (if IsPeakAt (joinMax α β) ⟨a + (k + 1), h⟩ then (1 : ℕ) else 0) else 0)) =
    ∑ x ∈ Finset.range b,
    (if h : x < b then (if IsPeakAt β ⟨x, h⟩ then (1 : ℕ) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hii : i < b := Finset.mem_range.mp hi
    have key := isPeakAt_joinMax_right α β i hii
    have hbound : a + (i + 1) < a + b + 1 := by omega
    rw [dite_eq_left hbound, dite_eq_left hii]
    have peq : (⟨a + (i + 1), hbound⟩ : Fin (a + b + 1)) = ⟨a + 1 + i, by omega⟩ := by
      apply Fin.ext
      change a + (i + 1) = a + 1 + i
      omega
    rw [peq]
    by_cases hpk : IsPeakAt β ⟨i, hii⟩
    · have h1 : IsPeakAt (joinMax α β) ⟨a + 1 + i, by omega⟩ := key.mpr hpk
      simp only [h1, hpk, ite_true]
    · have h1 : ¬ IsPeakAt (joinMax α β) ⟨a + 1 + i, by omega⟩ :=
      fun h => hpk (key.mp h)
      simp only [h1, hpk, ite_false]
  have e3 : (if h : a + 0 < a + b + 1 then
    (if IsPeakAt (joinMax α β) ⟨a + 0, h⟩ then (1 : ℕ) else 0) else 0) =
    (if a = 0 ∨ b = 0 then 0 else 1) := by
    have hbound : a + 0 < a + b + 1 := by omega
    rw [dite_eq_left hbound]
    have key := isPeakAt_joinMax_mid α β
    by_cases h0 : a = 0 ∨ b = 0
    · have h1 : ¬ IsPeakAt (joinMax α β) ⟨a + 0, hbound⟩ := fun h => (key.mp h) h0
      simp only [h1, ite_false, h0, ite_true]
    · have h1 : IsPeakAt (joinMax α β) ⟨a + 0, hbound⟩ := key.mpr h0
      simp only [h1, ite_true, h0, ite_false]
  omega

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[card_filter_add_eq_sum_antidiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma card_filter_add_eq_sum_antidiagonal {X Y : Type*} (s : Finset X) (t : Finset Y)
  (f : X → ℕ) (g : Y → ℕ) (k : ℕ) :
  ((s ×ˢ t).filter (fun p => f p.1 + g p.2 = k)).card =
  ∑ q ∈ Finset.HasAntidiagonal.antidiagonal k,
    (s.filter (fun x => f x = q.1)).card * (t.filter (fun y => g y = q.2)).card := by
  have hmaps : Set.MapsTo (fun p : X × Y => (f p.1, g p.2))
    (((s ×ˢ t).filter (fun p => f p.1 + g p.2 = k)) : Set (X × Y))
    (Finset.HasAntidiagonal.antidiagonal k) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hp.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro q hq
  have hmem : q.1 + q.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  have hfib : Finset.filter (fun p : X × Y => (f p.1, g p.2) = q)
    ((s ×ˢ t).filter (fun p => f p.1 + g p.2 = k)) =
    (s.filter (fun x => f x = q.1)) ×ˢ (t.filter (fun y => g y = q.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hs, ht⟩, -⟩, hpair⟩
      have h1 : f p.1 = q.1 := congrArg Prod.fst hpair
      have h2 : g p.2 = q.2 := congrArg Prod.snd hpair
      exact ⟨⟨hs, h1⟩, ht, h2⟩
    · rintro ⟨⟨hs, h1⟩, ht, h2⟩
      refine ⟨⟨⟨hs, ht⟩, ?_⟩, ?_⟩
      · omega
      · exact Prod.ext h1 h2
  rw [hfib, Finset.card_product]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[peakV_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma peakV_zero (x : ℕ) : peakV 0 x = 0 := by
  unfold peakV
  simp

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[peakV_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma peakV_succ_eq (n p : ℕ) :
  peakV (n + 1) p = 2 ^ (n + 1 - p - 1) * Nat.choose n p := by
  unfold peakV
  have h1 : n + 1 ≠ 0 := by omega
  simp only [h1, ite_false, Nat.add_sub_cancel]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[peakV_succ_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma peakV_succ_add (n p : ℕ) :
  peakV (n + 1) (p + 1) = 2 * peakV n (p + 1) + peakV n p := by
  by_cases hn : n = 0
  · subst hn
    rw [peakV_succ_eq 0 (p + 1)]
    have hC : Nat.choose 0 (p + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hC, mul_zero, peakV_zero (p + 1), peakV_zero p, mul_zero, add_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [peakV_succ_eq (m + 1) (p + 1), peakV_succ_eq m (p + 1), peakV_succ_eq m p]
    have e1 : m + 1 + 1 - (p + 1) - 1 = m - p := by omega
    have e2 : m + 1 - (p + 1) - 1 = m - p - 1 := by omega
    have e3 : m + 1 - p - 1 = m - p := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ' m p, mul_add]
    by_cases hpm : p + 1 ≤ m
    · have hpow : (2 : ℕ) ^ (m - p) = 2 * 2 ^ (m - p - 1) := by
      obtain ⟨t, ht⟩ : ∃ t, m - p = t + 1 := ⟨m - p - 1, by omega⟩
      rw [ht, pow_succ, Nat.add_sub_cancel]
      ring
      rw [hpow]
      ring
    · have hC0 : Nat.choose m (p + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hC0]
      ring

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[peakV_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma peakV_succ_zero (n : ℕ) :
  peakV (n + 1) 0 = 2 * peakV n 0 + (if n = 0 then 1 else 0) := by
  by_cases hn : n = 0
  · subst hn
    rw [peakV_succ_eq 0 0, show (0 : ℕ) + 1 - 0 - 1 = 0 by omega,
      pow_zero, Nat.choose_zero_right, one_mul, peakV_zero 0]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [peakV_succ_eq (m + 1) 0, peakV_succ_eq m 0]
    have e1 : m + 1 + 1 - 0 - 1 = m + 1 := by omega
    have e2 : m + 1 - 0 - 1 = m := by omega
    have hn1 : m + 1 ≠ 0 := by omega
    rw [e1, e2]
    simp only [hn1, ite_false, Nat.choose_zero_right, mul_one, add_zero]
    rw [pow_succ]
    ring

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[peakU_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma peakU_eq : peakU = PowerSeries.X * (1 + peakU + peakU) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul]
    unfold peakU
    rw [PowerSeries.coeff_mk]
    simp
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, map_add, map_add, PowerSeries.coeff_one]
    unfold peakU
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hm1 : m + 1 ≠ 0 := by omega
      have hpow : (2 : ℕ) ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]
        ring
      simp only [hm1, hm, ite_false, Nat.add_sub_cancel, zero_add]
      exact hpow

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[coeff_peakU_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma coeff_peakU_succ (n : ℕ) :
  PowerSeries.coeff (n + 1) peakU = 2 ^ n := by
  unfold peakU
  rw [PowerSeries.coeff_mk]
  have hn1 : n + 1 ≠ 0 := by omega
  have e2 : n + 1 - 1 = n := by omega
  simp only [hn1, ite_false]
  rw [e2]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[coeff_peakU_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma coeff_peakU_pow (n p : ℕ) :
  PowerSeries.coeff n (peakU ^ (p + 1)) = peakV n p := by
  induction n generalizing p with
  | zero =>
    have h0 : PowerSeries.coeff 0 peakU = 0 := by
      unfold peakU
      rw [PowerSeries.coeff_mk]
      simp
    have hc : PowerSeries.constantCoeff peakU = 0 := by
      rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
    rw [peakV_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hc]
    exact zero_pow (by omega)
  | succ n ih =>
    cases p with
    | zero =>
      rw [pow_one, coeff_peakU_succ n, peakV_succ_eq n 0]
      have e : n + 1 - 0 - 1 = n := by omega
      rw [e, Nat.choose_zero_right, mul_one]
    | succ q =>
      have h1 : ∀ v : PowerSeries ℕ,
        v * peakU = v * (PowerSeries.X * (1 + peakU + peakU)) := by
        intro v
        conv_lhs => rw [peakU_eq]
      rw [pow_succ peakU (q + 1), h1]
      have hexpand : peakU ^ (q + 1) * (PowerSeries.X * (1 + peakU + peakU)) =
        PowerSeries.X * peakU ^ (q + 1) + PowerSeries.X * peakU ^ (q + 1 + 1) +
        PowerSeries.X * peakU ^ (q + 1 + 1) := by
        rw [pow_succ peakU (q + 1)]
        ring
      rw [hexpand]
      simp only [map_add, PowerSeries.coeff_succ_X_mul, ih q, ih (q + 1)]
      rw [peakV_succ_add n q]
      ring

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[sum_antidiagonal_peakV_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma sum_antidiagonal_peakV_mul (n a b : ℕ) :
  (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, peakV q.1 a * peakV q.2 b) =
  peakV n (a + b + 1) := by
  have h1 : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal n,
    peakV q.1 a * peakV q.2 b =
    PowerSeries.coeff q.1 (peakU ^ (a + 1)) *
      PowerSeries.coeff q.2 (peakU ^ (b + 1)) := by
    intro q _
    rw [coeff_peakU_pow, coeff_peakU_pow]
  have hsum : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, peakV q.1 a * peakV q.2 b) =
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      PowerSeries.coeff q.1 (peakU ^ (a + 1)) *
        PowerSeries.coeff q.2 (peakU ^ (b + 1))) :=
    Finset.sum_congr rfl h1
  rw [hsum, ← PowerSeries.coeff_mul, ← pow_add]
  have hexp : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
  rw [hexp, coeff_peakU_pow]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[sum_peakV_catalan_conv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma sum_peakV_catalan_conv (n k' : ℕ) :
  (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k',
    (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
  peakV n (2 * k' + 1) * catalan (k' + 1) := by
  have hinner : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k',
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
    (catalan p.1 * catalan p.2) * peakV n (2 * k' + 1) := by
    intro p hp
    have hmem : p.1 + p.2 = k' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hstep : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
      (catalan p.1 * catalan p.2) *
        (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
          peakV q.1 (2 * p.1) * peakV q.2 (2 * p.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hV : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      peakV q.1 (2 * p.1) * peakV q.2 (2 * p.2)) = peakV n (2 * k' + 1) := by
      have h := sum_antidiagonal_peakV_mul n (2 * p.1) (2 * p.2)
      have hexp : 2 * p.1 + 2 * p.2 + 1 = 2 * k' + 1 := by omega
      rwa [hexp] at h
    rw [hstep, hV]
  have hsum : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k',
    ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
    (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k',
      (catalan p.1 * catalan p.2) * peakV n (2 * k' + 1)) :=
    Finset.sum_congr rfl hinner
  have hcat : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k', catalan p.1 * catalan p.2) =
    catalan (k' + 1) := (catalan_succ' k').symm
  rw [Finset.sum_comm, hsum, ← Finset.sum_mul, hcat]
  ring

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[sum_range_fiber_eq_sum_antidiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma sum_range_fiber_eq_sum_antidiagonal (n : ℕ) (F : ℕ → ℕ) :
  (∑ b ∈ Finset.range n.succ, F b) =
  ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, F q.1 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end MetaMathlibExt.Peak231

namespace MetaMathlibExt.Peak231

/--
[peakT_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma peakT_succ (n k : ℕ) : peakT (n + 1) k = peakRec peakT n k := by
  have hT0 : ∀ j : ℕ, peakT 0 j = (if j = 0 then 1 else 0) := by
    intro j
    unfold peakT
    by_cases hj : j = 0
    · subst hj
      simp
    · have hC : Nat.choose (0 - 1) (2 * j) = 0 := by
      have h1 : (0:ℕ) - 1 = 0 := by omega
      rw [h1]
      apply Nat.choose_eq_zero_of_lt
      omega
      rw [hC]
      simp only [mul_zero, zero_mul, hj, ite_false]
  have hTV : ∀ m j : ℕ, m ≠ 0 → peakT m j = peakV m (2 * j) * catalan j := by
    intro m j hm
    unfold peakT peakV
    simp only [hm, ite_false]
  have hV0 : ∀ x : ℕ, peakV 0 x = 0 := by
    intro x
    unfold peakV
    simp only [ite_true]
  have edgeConvL : ∀ b k : ℕ, peakConv peakT 0 b k = peakT b k := by
    intro b k
    unfold peakConv
    have h1 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      peakT 0 p.1 * peakT b p.2 = (if p = (0, k) then peakT b k else 0) := by
      intro p hp
      have hmem : p.1 + p.2 = k :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases he : p = (0, k)
      · simp only [he, ite_true]
        have e0 : peakT 0 (0, k).1 = 1 := by
          rw [hT0]
          have c0 : (0, k).1 = 0 := rfl
          rw [c0]
          simp only [ite_true]
        have e1 : peakT b (0, k).2 = peakT b k := rfl
        rw [e0, e1, one_mul]
      · have h1 : p.1 ≠ 0 := by
        intro h1
        apply he
        have h2 : p.2 = k := by omega
        exact Prod.ext h1 h2
        simp only [he, ite_false]
        have e0 : peakT 0 p.1 = 0 := by
          simp only [hT0, h1, ite_false]
        rw [e0, zero_mul]
    have h2 : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      peakT 0 p.1 * peakT b p.2) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      (if p = (0, k) then peakT b k else 0) :=
      Finset.sum_congr rfl h1
    rw [h2]
    have hmem' : (0, k) ∈ Finset.HasAntidiagonal.antidiagonal k :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change (0:ℕ) + k = k; omega)
    rw [Finset.sum_ite_eq' _ (0, k) (fun _ => peakT b k), ite_eq_left hmem']
  have edgeConvR : ∀ a k : ℕ, peakConv peakT a 0 k = peakT a k := by
    intro a k
    unfold peakConv
    have h1 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      peakT a p.1 * peakT 0 p.2 = (if p = (k, 0) then peakT a k else 0) := by
      intro p hp
      have hmem : p.1 + p.2 = k :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases he : p = (k, 0)
      · simp only [he, ite_true]
        have e0 : peakT 0 (k, 0).2 = 1 := by
          rw [hT0]
          have c0 : (k, 0).2 = 0 := rfl
          rw [c0]
          simp only [ite_true]
        have e1 : peakT a (k, 0).1 = peakT a k := rfl
        rw [e0, e1, mul_one]
      · have h2 : p.2 ≠ 0 := by
        intro h2
        apply he
        have h1 : p.1 = k := by omega
        exact Prod.ext h1 h2
        simp only [he, ite_false]
        have e0 : peakT 0 p.2 = 0 := by
          simp only [hT0, h2, ite_false]
        rw [e0, mul_zero]
    have h2 : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      peakT a p.1 * peakT 0 p.2) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      (if p = (k, 0) then peakT a k else 0) :=
      Finset.sum_congr rfl h1
    rw [h2]
    have hmem' : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change k + (0:ℕ) = k; omega)
    rw [Finset.sum_ite_eq' _ (k, 0) (fun _ => peakT a k), ite_eq_left hmem']
  by_cases hn0 : n = 0
  · subst hn0
    have hL : peakT 1 k = (if k = 0 then 1 else 0) := by
      unfold peakT
      by_cases hk : k = 0
      · subst hk
        simp
      · have hC : Nat.choose (1 - 1) (2 * k) = 0 := by
        have h1 : (1:ℕ) - 1 = 0 := by omega
        rw [h1]
        apply Nat.choose_eq_zero_of_lt
        omega
        rw [hC]
        simp only [mul_zero, zero_mul, hk, ite_false]
    have h00 : peakRec peakT 0 k = peakConv peakT 0 0 k := by
      unfold peakRec
      rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      have hc : ((0, 0).1 = 0 ∨ (0, 0).2 = 0) := Or.inl rfl
      exact ite_eq_left hc
    have hR : peakRec peakT 0 k = (if k = 0 then 1 else 0) := by
      rw [h00, edgeConvL 0 k]
      exact hT0 k
    rw [hL, hR]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hSEM : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
      (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k
        else (if k = 0 then 0 else peakConv peakT q.1 q.2 (k - 1))) =
      (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0) +
      (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
        (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2))) := by
      intro q hq
      by_cases he : q.1 = 0 ∨ q.2 = 0
      · have hM0 : (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
        (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2))) = 0 := by
        by_cases hk : k = 0
        · simp only [hk, ite_true]
        · simp only [hk, ite_false]
          apply Finset.sum_eq_zero
          intro p _
          obtain h10 | h20 := he
          · rw [h10]
            simp only [hV0, zero_mul]
          · rw [h20]
            simp only [hV0, zero_mul, mul_zero]
        simp only [he, ite_true]
        rw [hM0, add_zero]
      · have hmid : ¬(q.1 = 0 ∨ q.2 = 0) := he
        have hqpair := not_or.mp hmid
        have hAB : peakConv peakT q.1 q.2 (k - 1) =
          (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
          (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) := by
          unfold peakConv
          apply Finset.sum_congr rfl
          intro p _
          rw [hTV q.1 p.1 hqpair.1, hTV q.2 p.2 hqpair.2]
        simp only [hmid, ite_false]
        rw [hAB, zero_add]
    have hEsplit : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
      (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0) =
      (if q = (0, m + 1) then peakT (m + 1) k else 0) +
      (if q = (m + 1, 0) then peakT (m + 1) k else 0) := by
      intro q hq
      have hmem : q.1 + q.2 = m + 1 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      by_cases h10 : q = (0, m + 1)
      · by_cases h20 : q = (m + 1, 0)
        · have hcon2 : (0:ℕ) = m + 1 := congrArg Prod.fst (h10.symm.trans h20)
          omega
        · have hq1 : q.1 = 0 := congrArg Prod.fst h10
          have hq2 : q.2 = m + 1 := by omega
          have hc : q.1 = 0 ∨ q.2 = 0 := Or.inl hq1
          have eE : peakConv peakT q.1 q.2 k = peakT (m + 1) k := by
            rw [hq1, hq2]
            exact edgeConvL (m + 1) k
          simp only [hc, ite_true]
          rw [eE]
          have hneq : (0, m + 1) ≠ (m + 1, 0) := by
            intro hcon
            have hfst : (0:ℕ) = m + 1 := congrArg Prod.fst hcon
            omega
          simp only [h10, ite_true, hneq, ite_false, add_zero]
      · by_cases h20 : q = (m + 1, 0)
        · have hq2 : q.2 = 0 := congrArg Prod.snd h20
          have hq1 : q.1 = m + 1 := by omega
          have hc : q.1 = 0 ∨ q.2 = 0 := Or.inr hq2
          have eE : peakConv peakT q.1 q.2 k = peakT (m + 1) k := by
            rw [hq1, hq2]
            exact edgeConvR (m + 1) k
          simp only [hc, ite_true]
          rw [eE]
          have hneq : (m + 1, 0) ≠ (0, m + 1) := by
            intro hcon
            have hfst : m + 1 = (0:ℕ) := congrArg Prod.fst hcon
            omega
          simp only [h20, hneq, ite_false, ite_true, zero_add]
        · have hne : ¬(q.1 = 0 ∨ q.2 = 0) := by
          rintro (h1 | h2)
          · apply h10
            have h2' : q.2 = m + 1 := by omega
            exact Prod.ext h1 h2'
          · apply h20
            have h1' : q.1 = m + 1 := by omega
            exact Prod.ext h1' h2
          simp only [hne, ite_false, h10, ite_false, h20, ite_false, add_zero]
    have hEsum : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
      (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0)) =
      peakT (m + 1) k + peakT (m + 1) k := by
      have h1 : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0)) =
        ∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        ((if q = (0, m + 1) then peakT (m + 1) k else 0) +
        (if q = (m + 1, 0) then peakT (m + 1) k else 0)) :=
        Finset.sum_congr rfl hEsplit
      rw [h1, Finset.sum_add_distrib]
      have hmem1 : (0, m + 1) ∈ Finset.HasAntidiagonal.antidiagonal (m + 1) :=
        Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change (0:ℕ) + (m + 1) = m + 1; omega)
      have s1 : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if q = (0, m + 1) then peakT (m + 1) k else 0)) = peakT (m + 1) k := by
        rw [Finset.sum_ite_eq' _ (0, m + 1) (fun _ => peakT (m + 1) k), ite_eq_left hmem1]
      have hmem2 : (m + 1, 0) ∈ Finset.HasAntidiagonal.antidiagonal (m + 1) :=
        Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change (m + 1) + (0:ℕ) = m + 1; omega)
      have s2 : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if q = (m + 1, 0) then peakT (m + 1) k else 0)) = peakT (m + 1) k := by
        rw [Finset.sum_ite_eq' _ (m + 1, 0) (fun _ => peakT (m + 1) k), ite_eq_left hmem2]
      rw [s1, s2]
    have hMsum : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
      (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
        (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)))) =
      (if k = 0 then 0 else peakV (m + 1) (2 * (k - 1) + 1) * catalan ((k - 1) + 1)) := by
      by_cases hk : k = 0
      · simp only [hk, ite_true, Finset.sum_const_zero]
      · simp only [hk, ite_false]
        rw [sum_peakV_catalan_conv]
    have hSE : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
      (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k
        else (if k = 0 then 0 else peakConv peakT q.1 q.2 (k - 1)))) =
      (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
      ((if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0) +
      (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
        (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2))))) :=
      Finset.sum_congr rfl hSEM
    unfold peakRec
    rw [hSE, Finset.sum_add_distrib, hEsum, hMsum]
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true, add_zero]
      rw [hTV (m + 1 + 1) 0 (by omega), hTV (m + 1) 0 (by omega)]
      simp only [catalan_zero, mul_one]
      have hN10 := peakV_succ_zero (m + 1)
      rw [hN10]
      have hm1 : ¬(m:ℕ) + 1 = 0 := by omega
      simp only [hm1, ite_false, add_zero]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj1 : ¬(j:ℕ) + 1 = 0 := by omega
      have hj2 : j + 1 - 1 = j := by omega
      rw [ite_eq_right hj1, hj2]
      rw [hTV (m + 1 + 1) (j + 1) (by omega), hTV (m + 1) (j + 1) (by omega)]
      have hidx : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [hidx]
      have hN10 := peakV_succ_add (m + 1) (2 * j + 1)
      rw [hN10]
      ring

end MetaMathlibExt.Peak231

/--
[card_permutations_avoiding_231_with_peak_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma card_permutations_avoiding_231_with_peak_count_eq
  {n k : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
    (Finset.univ.filter (fun i : Fin n =>
    ∃ iPrev iNext : Fin n,
    iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
    σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
    2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * Nat.choose (2 * k) k /
    (k + 1) := by
-- proof
  apply MetaMathlibExt.card_permutations_avoiding_231_with_peak_count n k hn


-- created on 2026-10-20
-- updated on 2026-10-23
