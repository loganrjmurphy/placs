import Assurance.Product.Analytic
import Assurance.ProductLine.vTemplate
set_option autoImplicit false
open SPL
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
def asTemplate {A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
(T : vAnalyticTemplate A B C α β γ Φ) (pc : PC 𝔽) : vTemplate A B α β Φ  :=
{ parentPC := pc,
  parent := T.parent,
  apply := λ (m, x) =>
    (.pred pc T.inputRel (m,x))::(.pred pc T.inputPred x)::(.pred pc T.outputPred (T.F x))::(.atom pc <| ∀ k , T.fpred k (T.f k))::(.atom pc <| isLift (Φ:=Φ) T.f T.F)::[]
}

def vAnalyticTemplate_apply
{A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
(T : vAnalyticTemplate A B C α β γ Φ) (pc : PC 𝔽) {a : α} {b : β} :
  (T.asTemplate pc : vTemplate A B α β Φ ).apply (a, b) = (.pred pc T.inputRel (a,b))::(.pred pc T.inputPred b)::(.pred pc T.outputPred (T.F b))::(.atom pc <| ∀ k , T.fpred k (T.f k))::(.atom pc (isLift (Φ:=Φ) T.f T.F))::[] :=
by rfl

def lift {A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
   (T : AnalyticTemplate A B C) (F : β → γ) : vAnalyticTemplate A B C α β γ Φ :=
  {parent := T.parent, inputRel := T.inputRel, inputPred := T.inputPred, outputPred := T.outputPred, fpred:=T.fpred, f := T.f, F := F}

def lift_valid {A B C α β γ: Type} {Φ : FeatModel 𝔽} [Var α A Φ] [Var β B Φ] [Var γ C Φ]
   {T : AnalyticTemplate A B C} (F : β → γ) {pc : PC 𝔽} :
    T.toTemplate.valid → ((lift T F (α := α) (Φ := Φ)).asTemplate pc).valid :=
by
  intro h
  rw [AnalyticTemplate.valid_def] at h
  rw [asTemplate,lift] ; simp
  intros a b prec c hc subs ; clear prec ; simp at *
  rcases subs with ⟨h1,h2,h3,h4,h5⟩
  rw [semantics, vGoal.derive_pred] at * ; simp at *
  rw [vGoal.pc] at * ; simp at *
  refine h (a ↓ c) (b ↓ c) ?a (h2 hc) ?b ?c
  . rw [prod_derive_def] at h1 ; simp at h1 ; exact h1 hc
  . rw [← h5 hc b c] ; exact h3 hc
  . intros k ; exact h4 hc k





end vAnalyticTemplate
