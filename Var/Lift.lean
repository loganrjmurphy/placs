import Var.Class

variable {F : Type} [FeatureSet F] {Φ : FeatModel F} [Var α A Φ] [Var β B Φ] [Var γ C Φ]

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
