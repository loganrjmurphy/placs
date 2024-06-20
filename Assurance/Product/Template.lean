import Assurance.Product.Properties
import Var.Data

set_option autoImplicit false

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

lemma invariant_iff {α : Type} {P : α → Prop} {t : Set α} :
  invariant P t ↔ ∀ x ∈ t, P x := Iff.rfl

def complete {α : Type} (prod : Set α ×  Family α) : Prop :=
  ∀ x ∈ prod.fst, ∃ t ∈ prod.snd, x ∈ t

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

lemma apply_def {α : Type} {P : α → Prop}  {s : Set α} {F : Family α}:
  (DomainDecomp P).apply (s, F) = GSN.undevGoals (F.map (Goal.pred (invariant P))) :=
  rfl

lemma prec_iff {α : Type} {P : α → Prop} (s : Set α) (F : Family α) :
  (DomainDecomp P).prec (s,F) ↔ ∀ x ∈ s, ∃ t ∈ F, x ∈ t :=
    by rw [DomainDecomp, ← complete_iff]


lemma parent_iff {α : Type} {P : α → Prop} (s : Set α)  :
  (DomainDecomp P).parent s ↔ ∀ x ∈ s, P x :=
    by rw [DomainDecomp, ← invariant_iff]

lemma subgoals_iff {α : Type} {P : α → Prop} {F : Family α} :
   (∀ g' ∈ List.map (Goal.pred (invariant P)) F, ⟦g'⟧)
   ↔ ∀ a ∈ F, ∀ x ∈ a, P x
  :=
   by
    simp only [List.mem_map, Finset.mem_toList, forall_exists_index, and_imp,
     forall_apply_eq_imp_iff₂,Goal.semantics_pred, invariant_iff]

end DomainDecomp


theorem domainDecompValid {α : Type}  {P : α → Prop} : Template.valid <| DomainDecomp P :=
by
  intro ⟨s,F⟩ hprec
  rw [DomainDecomp.prec_iff] at hprec
  rw [DomainDecomp.apply_def,GSN.refines] ; simp only
  rw [GSN.undevGoals_roots_inv, Goal.semantics_pred,DomainDecomp.parent_iff]
  rw [DomainDecomp.subgoals_iff]
  intros hsubs x hx
  replace hprec := hprec x hx
  rcases hprec with ⟨t, ht⟩
  exact hsubs t ht.left x ht.right
