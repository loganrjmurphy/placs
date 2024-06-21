import Assurance.Product.Properties
import Var.Data

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

def invariant {α : Type} (P : α → Prop) (t : Set α) : Prop :=
  ∀ x ∈ t, P x

@[simp]
lemma invariant_iff {α : Type} {P : α → Prop} {t : Set α} :
  invariant P t ↔ ∀ x ∈ t, P x := Iff.rfl

def complete {α : Type} (prod : Set α ×  Family α) : Prop :=
  ∀ x ∈ prod.fst, ∃ t ∈ prod.snd, x ∈ t

@[simp]
def complete_iff {α : Type} (s : Set α) (F : Family α) :
  complete (s, F) ↔ ∀ x ∈ s, ∃ t ∈ F, x ∈ t := by rw [complete]


noncomputable def DomainDecomp.apply {α : Type} (P : α → Prop)  (v: Family α) :  List GSN :=
   GSN.undevGoals <| v.map <| Goal.pred <| invariant P

noncomputable def DomainDecomp {α : Type} (P : α → Prop) : Template (Set α) (Family α) :=
  {
    parent := invariant P
    prec := complete
    apply := λ ⟨_, F⟩ => DomainDecomp.apply P F
  }

namespace DomainDecomp

@[simp]
lemma apply_def {α : Type} {P : α → Prop}  {s : Set α} {F : Family α}:
  (DomainDecomp P).apply (s, F) = GSN.undevGoals (F.map (Goal.pred (invariant P))) :=
  rfl

@[simp]
lemma prec_iff {α : Type} {P : α → Prop} (s : Set α) (F : Family α) :
  (DomainDecomp P).prec (s,F) ↔ ∀ x ∈ s, ∃ t ∈ F, x ∈ t :=
    by rw [DomainDecomp, ← complete_iff]

@[simp]
lemma parent_iff {α : Type} {P : α → Prop} (s : Set α)  :
  (DomainDecomp P).parent s ↔ ∀ x ∈ s, P x :=
    by rw [DomainDecomp, ← invariant_iff]

@[simp]
lemma subgoals_iff {α : Type} {P : α → Prop} {F : Family α} :
   (∀ g' ∈ List.map (Goal.pred (invariant P)) F, ⟦g'⟧)
   ↔ ∀ a ∈ F, ∀ x ∈ a, P x
  :=
   by
    simp only [List.mem_map, Finset.mem_toList, forall_exists_index, and_imp,
     forall_apply_eq_imp_iff₂,Goal.pred_semantics, invariant_iff]

def refinement_condition {α : Type} {P : α → Prop} : (DomainDecomp P).valid ↔
  ∀ s : Set α, ∀ F : Family α, (∀ x ∈ s, ∃ t ∈ F, x ∈ t) → (∀ a ∈ F, ∀ x ∈ a, P x) → ∀ x ∈ s, P x :=
by
  simp only [Template.valid,GSN.refines_def, Goal.pred_semantics, parent_iff, Prod.forall, prec_iff, apply_def,
    GSN.undevGoals_roots_inv, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    invariant_iff]


end DomainDecomp




theorem domainDecompValid {α : Type}  {P : α → Prop} : Template.valid <| DomainDecomp P :=
by
  -- intro ⟨s,F⟩
  rw [DomainDecomp.refinement_condition]
  intros s F hprec hsubs x hx
  rcases hprec x hx with ⟨t, ⟨tmem, xmem⟩⟩
  exact hsubs t tmem x xmem
