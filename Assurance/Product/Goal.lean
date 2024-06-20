import Mathlib
set_option autoImplicit false

inductive Goal
| atom (p : Prop) : Goal
| pred {α : Type} (P : α → Prop) (x : α) : Goal

instance : Coe Prop Goal := ⟨Goal.atom⟩

namespace Goal

def semantics : Goal → Prop
| .atom p => p
| .pred P x => P x

notation "⟦"G"⟧" => semantics G

lemma semantics_atom {p : Prop} : semantics p = p := rfl
lemma semantics_pred {α : Type} {P : α → Prop} {x : α} : semantics (.pred P x) = P x := rfl

end Goal
