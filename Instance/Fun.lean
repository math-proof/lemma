import Structure.Fun

namespace Fun

instance : CoeFun (Fun ι α) (fun _ => ι → α) where
  coe := toFun

instance : GetElem (Fun ι α) ι α (fun _ _ => True) where
  getElem f i _ := f.toFun i

end Fun
