import Assurance.GSN.Template.Basic

set_option autoImplicit false

structure AnalyticTemplate (α X Y: Type) where
 parent : α → Prop
 f : X → Y
 fpred : X → Y → Prop
 inputRel : α × X → Prop
 inputPred : X → Prop
 outputPred : Y → Prop

namespace AnalyticTemplate

variable {α X Y : Type}

def apply (T : AnalyticTemplate α X Y) : α × X → List Goal := λ (a, x) =>
[     .atom (∀ x  : X, T.fpred x (T.f x)),
      Goal.pred T.inputRel (a,x) ,
      Goal.pred T.inputPred x    ,
      Goal.pred T.outputPred (T.f x)]

@[simp]
lemma apply_def {T : AnalyticTemplate α X Y} {a : α} {x : X}  : T.apply (a, x) =
  [   .atom (∀ x  : X, T.fpred x (T.f x)),
      Goal.pred T.inputRel (a,x),
      Goal.pred T.inputPred x,
      Goal.pred T.outputPred (T.f x)] := rfl

def toTemplate  (T : AnalyticTemplate α X Y) : Template α X :=
{ parent := T.parent,
  apply := λ x => GSN.undevGoals <| T.apply x
}

def prec_trivial {T : AnalyticTemplate α X Y} {a : α} {x : X}  : T.toTemplate.prec (a, x) :=
  by simp only [toTemplate]

@[simp]
lemma strategy_root_opt {g g' : Goal} {l : List GSN} :
    some g = (GSN.strategy g' l).root? ↔ g = g' :=
  by
    simp only [ne_eq, not_false_eq_true, GSN.root_opt_elim, GSN.strategy_root, eq_comm]

lemma mem_analytic_subgoals_disj  {T : AnalyticTemplate α X Y}  {g : Goal}  {a : α} {x : X} :
    g ∈ GSN.roots ((toTemplate T).apply (a, x)) ↔
  (g = ∀ x  : X, T.fpred x (T.f x)) ∨
  (g = Goal.pred T.inputRel (a,x)) ∨
  (g = Goal.pred T.inputPred x) ∨
  (g = Goal.pred T.outputPred (T.f x)) :=
    by
      simp only [GSN.roots, toTemplate, GSN.undevGoals, apply_def, List.map_cons, List.map_nil,
        List.reduceOption_mem_iff, List.mem_cons, ne_eq, not_false_eq_true, GSN.root_opt_elim,
        GSN.strategy_root, List.mem_singleton]
      tauto

lemma valid_def {T : AnalyticTemplate α X Y} :
  T.toTemplate.valid ↔
    ∀ (a : α) (x : X),
      T.inputRel (a,x) → T.inputPred x → T.outputPred (T.f x) → (∀ k, T.fpred k (T.f k)) → T.parent a :=
by
  rw [Template.valid]
  constructor
  . intros h a x rel inp outp fpred
    apply h (a, x) (prec_trivial)
    intros g' hg'
    rw [mem_analytic_subgoals_disj] at hg'
    cases' hg' with hg' hg' <;> cases' hg' with hg' hg'
    . rwa [Goal.atom_semantics]
    . rwa [hg', Goal.pred_semantics]
    . cases' hg' with hg' hg' <;> rwa [hg', Goal.pred_semantics]
  . intros h a prec ; clear prec ; cases' a with a x
    intros subs
    rw [Goal.pred_semantics]
    apply h a x
    . apply subs (Goal.pred T.inputRel (a,x)) (by rw [mem_analytic_subgoals_disj]; tauto)
    . apply subs (Goal.pred T.inputPred x) (by rw [mem_analytic_subgoals_disj]; tauto)
    . apply subs (Goal.pred T.outputPred (T.f x)) (by rw [mem_analytic_subgoals_disj]; tauto)
    . apply subs (∀ k, T.fpred k (T.f k)) (by rw [mem_analytic_subgoals_disj]; tauto)

end AnalyticTemplate
