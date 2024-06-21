import Assurance.Product.Analytic
import Assurance.ProductLine.vTemplate
set_option autoImplicit false

variable {𝔽 : Type} [FeatureSet 𝔽]

structure vAnalyticTemplate (A B C α β γ: Type) (Φ : FeatModel 𝔽) [Var α A Φ] [Var β B Φ] [Var γ C Φ] where
 parent : A → Prop
 f : B → C
 F : β → γ
 inputRel : A × B → Prop
 inputPred : B → Prop
 outputPred : C → Prop
 fpred : B → C → Prop

namespace vAnalyticTemplate

def vAnalyticTemplate_apply
{A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
(T : vAnalyticTemplate A B C α β γ Φ) (pc : PC 𝔽) (x : α × β) : List (vGoal Φ) :=
  ((vGoal.pred pc T.inputRel x)::(.pred pc T.inputPred x.2)::(.pred pc T.outputPred (T.F x.2))::(.atom pc <| ∀ k , T.fpred k (T.f k))::(.atom pc (isLift (Φ:=Φ) T.f T.F))::[])


def lift {A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
   (T : AnalyticTemplate A B C) (F : β → γ) : vAnalyticTemplate A B C α β γ Φ :=
  {parent := T.parent, inputRel := T.inputRel, inputPred := T.inputPred, outputPred := T.outputPred, fpred:=T.fpred, f := T.f, F := F}

def valid  {A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
(T : vAnalyticTemplate A B C α β γ Φ) (pc : PC 𝔽) : Prop :=
  ∀ c : Config Φ, c ⊨ pc →
    ∀ (x : α × β),
      (∀ g ∈ (vAnalyticTemplate_apply T pc x) ↓ c, ⟦g⟧) → ⟦(vGoal.pred (Φ:=Φ) pc T.parent x.1) ↓ c⟧



def lift_valid {A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
   {T : AnalyticTemplate A B C} (F : β → γ) {pc : PC 𝔽} :
    T.toTemplate.valid →
      valid ((lift T F (α := α) (Φ := Φ))) pc :=
by
  intro h
  rw [AnalyticTemplate.valid_def] at h
  rw [lift]
  rw [valid]
  intros c hc inp
  rcases inp with ⟨a, d⟩
  intros subs
  simp only
  rw [vGoal.derive_pred, Goal.pred_semantics]
  rw [vAnalyticTemplate_apply] at subs
  simp at subs
  rw [vTemplate.list_vgoal_derive_def] at subs
  simp at subs
  simp [vGoal.pc,hc] at *
  rcases subs with ⟨h1,h2,h3,h4,h5⟩
  rw [vGoal.derive_pred] at *
  apply h (a ↓ c) (d↓ c)
  . apply h1
  . apply h2
  . rw [← h5 (d) c] ; apply h3
  . exact h4




end vAnalyticTemplate
