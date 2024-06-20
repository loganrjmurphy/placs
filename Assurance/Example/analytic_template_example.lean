import Assurance.Example.gsn_example
import Assurance.Product.Analytic

-- for simplicity, make model checking binary
opaque modelChecker : LTS × CTL → Bool

def modelCheckingTemplate :
  AnalyticTemplate (Set Traces × Set Traces) (LTS × CTL) Bool :=
  {
    parent := Inclusion
    f := modelChecker
    fpred := λ (input : LTS × CTL) (output : Bool) ↦ (output = true) ↔ execs input.1 ⊆ words input.2
    inputRel := λ (data : ((Set Traces × Set Traces) ×  (LTS × CTL))) ↦
      modelCorrect (data.2.1, data.1.1) ∧ specCorrect (data.2.2, data.1.2)
    inputPred := λ _ => true
    outputPred := λ output => output = true
  }


theorem modelCheckingValid :  modelCheckingTemplate.toTemplate.valid :=
  by
    rw [modelCheckingTemplate, AnalyticTemplate.toTemplate]
    simp
    intros inp
    rcases inp with ⟨⟨ B,P⟩, ⟨M, φ⟩⟩
    simp_all
    rw [Goal.semantics_pred]
    intro subs
    rw [AnalyticTemplate.apply_def] at subs
    simp at subs
    rw [GSN.undevGoals_roots_inv] at subs
    simp at subs
    rcases subs with ⟨h1,⟨h2,h3⟩,h4,h5⟩
    rw [Goal.semantics_pred] at *  ; clear h4
    rw [Goal.semantics_atom] at *
    intros b hb
    rw [modelCorrect,specCorrect] at *
    simp at *
    have : B ⊆ execs M := Eq.subset (id (Eq.symm h2))
    replace this := this hb
    replace h1 := (h1 M φ).mp h5
    rw [← h3]
    exact h1 this
