import Assurance.Product.GSN
import Var.Data

set_option autoImplicit false

open scoped Goal

structure Template (α D : Type) where
  parent : α → Prop
  apply : α × D → List Goal
  prec : α × D → Prop := λ _ => True

structure verifTemplate (α D : Type) extends Template α D where
  verif : α × D → Bool
  verif_sound : ∀ (x : α × D), verif x ↔ prec x

namespace Template


def valid {α D : Type} (T : Template α D) : Prop :=
  ∀ x, T.prec x → GSN.refines (Goal.pred T.parent x.fst) (T.apply x)

end Template

noncomputable def domainDecomp {α : Type} (P : α → Prop) : Template (Set α) (Family α) :=
  {
    parent := λ s => ∀ x ∈ s, P x
    prec := λ ⟨s, F⟩ => ∀ x ∈ s, ∃ t ∈ F, x ∈ t
    apply := λ ⟨_, F⟩ => F.toList.map (λ s ↦ (∀ x ∈ ., P x) ⬝ s)
  }

lemma domainDecomp_apply {α : Type} {P : α → Prop}  {s : Set α} {F : Family α}:
  (domainDecomp P).apply (s, F) = F.toList.map ((λ s ↦ (∀ x ∈ ., P x) ⬝ s)) :=
  rfl


theorem domainDecompValid {α : Type}  {P : α → Prop} : Template.valid <| domainDecomp P :=
by
  intros x complete subs
  rw [Goal.semantics_pred]
  rw [domainDecomp_apply] at subs
  intros k mem
  rcases complete k mem with ⟨T,Tmem, kmem⟩
  replace subs := subs ((∀ x ∈ ., P x) ⬝ T) (by apply List.mem_map_of_mem; rwa [Finset.mem_toList])
  rw [Goal.semantics_pred] at subs
  exact subs k kmem
