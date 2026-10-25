import Instance.Analysis.Section_3_1.Part5
import Lemma.Set.Subset.of.Subset.Subset_SetTheory_Set_subset_trans
import Abbrev.Analysis.Section_3_1_order


namespace Chapter3

universe u v

variable [SetTheory]

open SetTheory

open SetTheory.Set

/-- Sets have a minimal element. -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

end Chapter3
