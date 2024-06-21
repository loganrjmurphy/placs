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

@[simp]
lemma atom_semantics {p : Prop} : semantics p = p := rfl

@[simp]
lemma pred_semantics {α : Type} {P : α → Prop} {x : α} : semantics (.pred P x) = P x := rfl

end Goal
