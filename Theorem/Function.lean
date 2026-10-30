import Abbrev.Difference
import Abbrev.Subst
import Def.Data.List.List.Basic
import Def.Subst
import Syntax.Subst
import Notation.Fun
import Structure.Fun
import Syntax.Fun
import Syntax.Subst


@[simp]
theorem Subst.eq_app {α : Sort*} {β : Sort*} (f : α → β) (a : α) : «Subst» f a = f a :=
  rfl

namespace Fun

@[simp] theorem getElem_eq (f : Fun ι α) (i : ι) : f[i] = f.toFun i := rfl
@[simp] theorem coe_eq (f : Fun ι α) (i : ι) : f i = f.toFun i := rfl

@[simp]
theorem getSliceFrom_apply (f : Fun ℕ α) (t k : ℕ) :
    getSliceFrom f t k = f.toFun (t + k) := rfl

theorem getSliceFrom_def (f : Fun ℕ α) (t : ℕ) :
    getSliceFrom f t = fun k ↦ f.toFun (t + k) := rfl

@[simp]
theorem getSliceFrom_apply_notation (f : Fun ℕ α) (t k : ℕ) :
    f[t:] k = f.toFun (t + k) := rfl

theorem getSliceFrom_def_notation (f : Fun ℕ α) (t : ℕ) :
    f[t:] = fun k ↦ f.toFun (t + k) := rfl

@[simp]
theorem getSliceFrom_eq_function (f : Fun ℕ α) (t : ℕ) :
    getSliceFrom f t = Function.getSliceFrom f.toFun t := rfl

end Fun
