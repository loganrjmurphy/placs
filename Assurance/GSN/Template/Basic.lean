import Assurance.GSN.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Goal

structure Template (α D : Type) where
  parent : α → Prop
  apply : α × D → List GSN
  prec : α × D → Prop := λ _ => True

structure verifTemplate (α D : Type) extends Template α D where
  verif : α × D → Bool
  verif_sound : ∀ (x : α × D), verif x ↔ prec x

namespace Template

def valid {α D : Type} (T : Template α D) : Prop :=
  ∀ x, T.prec x → GSN.refines ((Goal.pred T.parent x.fst), (T.apply x))

end Template
