import SPL.Config
namespace SPL
set_option autoImplicit false
/- This file defines some notational typeclasses and definition for "variational types" and lifted functions.
 -/

/- This typeclass says that type B has a derivation operator to A given a configuration of Features.
   Intuitively, this means that B is a variability-aware extension of A. Or, more simply,
   B is a type of "product lines" of A  -/

universe u v

variable {F : Type} [FeatureSet F]
class Var (α  : Type u) (A : outParam  (Type v)) (Φ : FeatModel F) where
  derive : α  → Config Φ → A

infix:80  "↓"  => Var.derive

variable  {Φ : FeatModel F} {A α B β C γ : Type u} [Var α A Φ] [Var β B Φ] [Var γ C Φ]

instance  : Var (α × β) (A × B) Φ :=
  .mk $ λ ⟨x, y⟩ c => ⟨x ↓ c, y ↓ c⟩

instance : Var (α ⊕ β) (A ⊕ B)  Φ :=
  .mk $ λ x c => match x with | .inl a => .inl (a ↓ c) | .inr b => .inr (b ↓ c)

def prod_derive_def [Var α A Φ] [Var β B Φ] {a : α × β} {c : Config Φ} : a ↓ c = (a.1 ↓ c, a.2 ↓ c) := rfl

/- Lifted functions -/
def isLift  (f : A → B) (F : α → β) : Prop :=
  ∀ x : α, ∀ c : Config Φ, F x ↓ c = f (x ↓ c)

/- TODO : See if we can avoid needing explicit provision of feature model -/
notation:60 f "⇈" F "⬝" Φ  => isLift (Φ:=Φ) f F

variable   {f : A → B} {g : B → C}{F : α → β}

-- Lifted binary functions (for convenience)
def isLift₂ (f : A → B → C) (F : α → β → γ) : Prop :=
  ∀ x : α, ∀ y : β, ∀ c : Config Φ, F x y ↓ c= f (x ↓ c) (y ↓ c)

/- Composing lifted functions -/
lemma lift_comp
  {f : A → B}
  {g : B → C}
  {F : α → β}
  {G : β → γ}
  (h₁ : f ⇈ F ⬝ Φ)
  (h₂ : g ⇈ G ⬝ Φ) : (g ∘ f) ⇈ (G ∘ F ) ⬝ Φ :=
by
  intros x pc
  replace h₁ := h₁ x pc
  replace h₂ := h₂ (F x) pc
  rw [Function.comp_apply, Function.comp_apply, h₂, h₁]

end SPL
