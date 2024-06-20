import Assurance.Product.Template

set_option autoImplicit false

open scoped Goal

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

lemma apply_def {T : AnalyticTemplate α X Y} {a : α} {x : X}  : T.apply (a, x) =
  [   .atom (∀ x  : X, T.fpred x (T.f x)),
      Goal.pred T.inputRel (a,x),
      Goal.pred T.inputPred x,
      Goal.pred T.outputPred (T.f x)] := rfl

def toTemplate  (T : AnalyticTemplate α X Y) : Template α X :=
{ parent := T.parent,
  apply := λ x => GSN.undevGoals <| T.apply x
}

def prec_trivial {T : AnalyticTemplate α X Y} {a : α} {x : X}  : T.toTemplate.prec (a, x) = True :=
  by rfl

lemma strategy_root_opt {g g' : Goal} {l : List GSN} :
    some g = (GSN.strategy g' l).root? ↔ g = g' :=
  by
      have this : GSN.strategy g' l ≠ .nil := nofun
      rw [GSN.root_opt_elim (h:=this), GSN.strategy_root]
      tauto

lemma mem_analytic_subgoals_disj  {T : AnalyticTemplate α X Y}  {g : Goal}  {a : α} {x : X} :
    g ∈ GSN.roots ((toTemplate T).apply (a, x)) ↔
  (g = ∀ x  : X, T.fpred x (T.f x)) ∨
  (g = Goal.pred T.inputRel (a,x)) ∨
  (g = Goal.pred T.inputPred x) ∨
  (g = Goal.pred T.outputPred (T.f x)) :=
    by
      rw [GSN.roots,toTemplate] ; simp
      rw [apply_def,List.reduceOption_mem_iff,GSN.undevGoals]
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_singleton]
      constructor
      . intro h
        cases h with
        | inl h => left ; rwa [strategy_root_opt] at h
        | inr h =>
        cases h with
        | inl h => right ; left ; rwa [strategy_root_opt] at h
        | inr h =>
        cases h with
        | inl h => right ; right ; left ; rwa [strategy_root_opt] at h
        | inr h => simp only [List.not_mem_nil, or_false] at h ; right ; right ; right ; rwa [strategy_root_opt] at h
      . intro h
        cases h with
        | inl h => left ; rwa [strategy_root_opt]
        | inr h =>
        cases h with
        | inl h => right ; left ; rwa [strategy_root_opt]
        | inr h =>
        cases h with
        | inl h => right ; right ; left ; rwa [strategy_root_opt]
        | inr h => simp only [List.not_mem_nil, or_false] at h ; right ; right ; right ; left; rwa [strategy_root_opt]

lemma valid_def {T : AnalyticTemplate α X Y} :
  T.toTemplate.valid ↔
    ∀ (a : α) (x : X),
      T.inputRel (a,x) → T.inputPred x → T.outputPred (T.f x) → (∀ k, T.fpred k (T.f k)) → T.parent a :=
by
  rw [Template.valid]
  constructor
  . intros h a x rel inp outp fpred
    replace h := h (a, x)
    rw [prec_trivial] at h ; simp only [forall_true_left] at h
    apply h
    intros g' hg'
    rw [mem_analytic_subgoals_disj] at hg'
    cases' hg' with hg' hg' <;> cases' hg' with hg' hg'
    . rwa [Goal.semantics_atom]
    . rwa [hg', Goal.semantics_pred]
    . cases' hg' with hg' hg' <;> rwa [hg', Goal.semantics_pred]
  . intros h a prec ; clear prec ; cases' a with a x
    intros subs
    rw [Goal.semantics_pred]
    apply h a x
    apply subs (Goal.pred T.inputRel (a,x)) (by rw [mem_analytic_subgoals_disj]; tauto)
    apply subs (Goal.pred T.inputPred x) (by rw [mem_analytic_subgoals_disj]; tauto)
    apply subs (Goal.pred T.outputPred (T.f x)) (by rw [mem_analytic_subgoals_disj]; tauto)
    apply subs (∀ k, T.fpred k (T.f k)) (by rw [mem_analytic_subgoals_disj]; tauto)

end AnalyticTemplate
