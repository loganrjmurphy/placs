import Var.Data
import Assurance.ProductLine.Properties
import Assurance.Product.Template
import Mathlib.Tactic
set_option autoImplicit false
open vSet vGSN

variable {F : Type} [FeatureSet F]


-- structure vTemplate (A D α γ : Type) (Φ : FeatModel F) [Var α A Φ] [Var γ D Φ] where
--   parent : A → Prop
--   parentPC : PC F
--   apply : α × γ → List (vGSN Φ)
--   prec : α × γ → (Config Φ → Prop) := λ _ _ => True



structure vTemplate' (A D α γ : Type) (Φ : FeatModel F) [Var α A Φ] [Var γ D Φ] where
  parent : A → Prop
  parentPC : PC F
  apply : α × γ → List (vGSN Φ)
  prec : α × γ → Prop := λ _ => True


namespace vTemplate

variable {Φ : FeatModel F}

variable {A D α γ : Type} [Var α A Φ] [Var γ D Φ]

-- def valid  (T : vTemplate A D α γ Φ) : Prop :=
--  ∀ x d, (∀ c : Config Φ, c ⊨ T.parentPC → T.prec (x, d) c) →
--   vGSN.refines (vGoal.pred T.parentPC T.parent x) (T.apply (x, d))

instance : Var (Config Φ → Prop) Prop Φ := ⟨λ p c => p c⟩

lemma prop_derive_def {p' : Config Φ → Prop} {c : Config Φ} : p' ↓ c ↔ p' c :=
  Iff.rfl

-- def lift
--   (T : Template A D)
--   (apply' : α × γ → List (vGSN Φ))
--   (prec' : α × γ → (Config Φ →  Prop))
--   (pc : PC F) : vTemplate A D α γ Φ :=
--   {
--     parentPC := pc
--     parent := T.parent
--     apply := apply'
--     prec := prec'
--   }

def lift'
  (T : Template A D)
  (apply' : α × γ → List (vGSN Φ))
  (pc : PC F) : vTemplate' A D α γ Φ :=
  {
    parentPC := pc
    parent := T.parent
    apply := apply'
    prec := λ (x,d) => [Φ|pc] T.prec (x,d)
  }


def lift_precondition
  (prec : A × D → Prop) : α × γ → Prop :=
  λ ⟨x,d⟩ => [Φ] prec (x,d)


def lift_precondition_restrict
  (prec : A × D → Prop) (φ : PC F) : α × γ → Prop :=
  λ ⟨x,d⟩ => [Φ| φ] prec (x,d)

def lift_precondition_restrict_eq
  (prec : A × D → Prop) (φ : PC F) (x : α) (d : γ) :
  lift_precondition_restrict (Φ:=Φ) prec φ (x,d) = [Φ| φ] prec (x,d) := by rfl

def valid'  (T : vTemplate' A D α γ Φ) : Prop :=
 ∀ x d, T.prec (x, d) →
  vGSN.refines (vGoal.pred T.parentPC T.parent x) (T.apply (x, d))




def valid_lift_prec_iff
  {T : vTemplate' A D α γ Φ}
  {prec : A × D → Prop}
  (hprec : T.prec = lift_precondition_restrict (Φ:=Φ) prec T.parentPC) :
    valid' T ↔
      ∀ x d, [Φ| T.parentPC] prec (x,d) →
  vGSN.refines (vGoal.pred T.parentPC T.parent x) (T.apply (x, d)) :=
  by
    constructor
    . intros h x d vprf
      intros c hc
      apply h x d  ; clear h
      rw [hprec,lift_precondition_restrict] ; simp
      exact vprf
      exact hc
    .
      intros h x d h' c hc
      apply h x d  ; clear h
      rw [← lift_precondition_restrict_eq, ← hprec]
      exact h'
      exact hc

def valid_lift_iff
  {T : Template A D}
  (apply' : α × γ → List (vGSN Φ))
  (pc : PC F) :
    valid' (lift' T apply' pc)
     ↔
      ∀ x d, [Φ| pc] T.prec (x,d) →
  vGSN.refines (vGoal.pred pc T.parent x) (apply' (x, d)) :=
  by
    have :  (lift' T apply' pc).prec = lift_precondition_restrict (Φ:=Φ) T.prec pc :=
      by funext x ; rw [lift_precondition_restrict_eq, lift']
    exact valid_lift_prec_iff this


def lift_valid'
  (T : Template A D)
  (apply' : α × γ → List (vGSN Φ))
  (happly : isLift (Φ := Φ) T.apply apply')
   (pc : PC F) :
  T.valid → valid' (lift' T apply' pc) :=
  by
    intro h
    rw [valid_lift_iff]
    intros x d π
    rw [refines]
    intros c hc
    replace h := h ((x,d) ↓ c) (π c hc)
    replace happly := happly (x,d) c
    rw [← happly] at h
    exact h



-- def lift_valid
--   (T : Template A D)
--   (apply' : α × γ → List (vGSN Φ))
--   (prec' : α × γ → (Config Φ → Prop))
--   (happly : isLift (Φ := Φ) T.apply apply')
--   (hprec : isLift (Φ := Φ) T.prec prec')
--    (pc : PC F) :
--   T.valid → (lift T apply' prec' pc).valid :=
--   by
--     intro h
--     rw [lift,valid]
--     intros x d h'
--     simp at *
--     rw [refines]
--     intros c hc
--     replace h' := h' c hc
--     rw [isLift] at hprec
--     replace hprec := hprec (x,d) c
--     rw [prop_derive_def] at hprec
--     rw [hprec] at h'; clear hprec
--     rw [GSN.refines]
--     simp only
--     intros subs
--     rw [prod_derive_def] at * ; simp only
--     rw [vGoal.derive_pred, Goal.semantics_pred]
--     rw [Template.valid] at h
--     replace h := h (x ↓ c, d ↓ c) h'
--     apply h  ; clear h
--     intros g' hg'
--     replace subs := subs g'
--     apply subs
--     simp at *
--     rwa [happly (x,d) c]

def undevGoals  : List (vGoal Φ) → List (vGSN Φ) := List.map (vGSN.strategy . [])

lemma undevGoals_roots_inv (l : List (vGoal Φ)) : vGSN.roots (undevGoals l) = l :=
  by
    rw [vGSN.roots, undevGoals,List.map_eq_map, List.map_map]
    induction l with
    | nil => rfl
    | cons h t ih =>
      rw [List.map_cons, Function.comp_apply, List.cons.injEq, vGSN.root]
      simp only [true_and, ih]

-- namespace Finite

open Classical

def vComplete (s : vSet α F) (v : vFamily α F) : Prop :=
  ∀ c : Config Φ, ∀ x ∈ s ↓ c, ∃ T ∈ v ↓ c, x ∈ T

def vComplete_restrict (s : vSet α F) (v : vFamily α F) (pc : PC F) : Prop :=
  ∀ c : Config Φ, c ⊨ pc → ∀ x ∈ s ↓ c, ∃ T ∈ v ↓ c, x ∈ T

def vComplete_iff {s : vSet α F} {v : vFamily α F} :
  vComplete (Φ := Φ) s v ↔ [Φ] complete (s,v) :=
  by
    rw [vComplete, confInv]
    constructor
    . intros h c _
      rw [prod_derive_def, complete_iff]; simp only [set_idx]
      exact h c
    . intros h c
      replace h := h c (Config.sat_univ)
      rw [prod_derive_def, complete_iff] at h
      exact h

def vComplete_restrict_iff {s : vSet α F} {v : vFamily α F} {pc : PC F} :
  vComplete_restrict (Φ := Φ) s v pc ↔ [Φ| pc] complete (s,v) :=
  by
    rw [vComplete_restrict, confInv]
    constructor
    . intros h c hc
      rw [prod_derive_def, complete_iff]; simp only [set_idx]
      exact h c hc
    . intros h c hc
      replace h := h c hc
      rw [prod_derive_def, complete_iff] at h
      exact h

noncomputable def vDomainDecomp.apply {α : Type} [DecidableEq α]  {Φ : FeatModel F} (P : α → Prop) ( v: vFamily α F) : List (vGSN Φ) :=
  undevGoals <| v.map <| (λ ⟨t,pc'⟩ => vGoal.pred pc' (invariant P) (t, pc'))

noncomputable def vDomainDecomp.apply' {α : Type} [DecidableEq α]  {Φ : FeatModel F} (P : α → Prop) ( v: vSet α F ×  vFamily α F) : List (vGSN Φ) :=
  undevGoals <| v.2.map <| (λ ⟨t,pc'⟩ => vGoal.pred pc' (invariant P) (t, pc'))


instance : Var (List (vGoal Φ)) (List Goal) Φ :=
  ⟨
    λ l c =>
      l.filterMap ( λ g : vGoal Φ ↦ if c ⊨ g.pc then (g ↓ c) else none)
  ⟩

set_option pp.proofs true
theorem list_vgoal_derive_def {l : List (vGoal Φ)} {c : Config Φ} :
  l ↓ c = l.filterMap ( λ g : vGoal Φ ↦ if c ⊨ g.pc then (g ↓ c) else none) := rfl

theorem attach_map {α β : Type}
  {f : α → β}
  {h : α}
  {t : List α} :
  ((h :: t).map f).attach = ((f h)::t.map f).attach :=
  by
    simp


theorem undev_comm {Φ : FeatModel F} {l : List (vGoal Φ)} {c : Config Φ} :
  (undevGoals l)↓c =
  GSN.undevGoals (l ↓ c) :=
  by
    induction l with
    | nil =>
      rw [undevGoals, GSN.undevGoals, list_vgoal_derive_def,vGSN_list_derive_def,mapFilterNil,attachedMap]
      simp only [ne_eq, decide_not, List.map_nil, List.attach_nil, List.map_eq_map, List.filter_nil,
        List.filterMap_nil]
    | cons h t ih =>
      rw [list_vgoal_derive_def, vGSN_list_derive_def]
      by_cases hc : c ⊨ h.pc
      . simp [hc]
        rw [GSN.undevGoals]
        simp
        rw [← GSN.undevGoals]
        rw [← list_vgoal_derive_def]
        rw [← ih]
        -- rw [List.attach,List.attachWith]
        -- simp
        have : (h ⇐ [])↓ c ≠ GSN.nil :=
          by
            have := vGSN.derive_sat_iff_ne_nil (g:=h⇐[]) (c:=c)
            rw [vGSN.strategy_root] at this
            rwa [← this]
        rw [undevGoals]
        simp
        rw [vGSN_list_derive_def]
        simp
        rw [mapFilter_cons_pos]
        simp
        rw [vGSN.derive_strat_of_sat]
        rfl
        assumption
        simp_all only [ne_eq, not_false_eq_true]
        simp
        aesop
      . simp [hc]
        simp [GSN.undevGoals]
        rw [← GSN.undevGoals]
        rw [← list_vgoal_derive_def]
        rw [← ih]
        have : (h ⇐ [])↓ c = GSN.nil :=by
            have := vGSN.derive_sat_iff_ne_nil (g:=h⇐[]) (c:=c)
            rw [vGSN.strategy_root] at this
            aesop
        rw [undevGoals]
        simp
        rw [mapFilter_cons_neg]
        . rw [vGSN_list_derive_def]
        . simp
        . simpa



          -- simp [this]
        -- rw [vGSN_list_derive_def]
        -- simp
        -- rw [← List.attachWith]
        -- constructor
        -- . admit
        -- . admit

        -- rw [undevGoals] at *
        -- rw [list_vgoal_derive_def, vGSN_list_derive_def] at *
        -- simp only [List.map_cons] at *
        -- rw [mapFilterNil] at *
        -- rw [ih]
        -- rw [GSN.undevGoals] at *
        -- simp only [List.map_cons] at *
        -- rw [List.attach,List.attachWith] at *
        -- simp only [List.pmap, List.filterMap_cons] at *
        -- have : (h ⇐ [])↓ c ≠ GSN.nil :=
        --   by
        --     have := vGSN.derive_sat_iff_ne_nil (g:=h⇐[]) (c:=c)
        --     rw [vGSN.strategy_root] at this
        --     rwa [← this]
        -- simp only [this, ↓reduceIte, List.cons.injEq]
        -- constructor
        -- . rw [vGSN.derive_strat_of_sat hc]
        --   rfl
        -- .


        -- simp only [ne_eq, decide_not, List.map_eq_map]
        -- rw [GSN.undevGoals] at *
        -- simp [hc]
        -- rw [← list_vgoal_derive_def]
        -- rw [← ih]
        -- rw [List.attach,List.attachWith]
        -- simp only [List.pmap, List.map_cons]
        -- rw [List.filter_cons]
        -- simp only [Bool.not_eq_true', decide_eq_false_iff_not, ite_not]
        -- rw [vGSN.derive_strat_of_sat hc]
        -- simp only [↓reduceIte, List.cons.injEq, GSN.strategy.injEq, true_and]
        -- constructor
        -- . rw [vGSN_list_derive_def, mapFilterNil]; simp
        -- . rw [ih]





            --  = []





-- lemma domDecompLiftApply
--   {α : Type} [DecidableEq α]  {Φ : FeatModel F}
--   {P : α → Prop} :
--   isLift (Φ:=Φ) (α := vFamily α F) (β := List (vGSN Φ)) (DomainDecomp.apply P) (vDomainDecomp.apply P)  :=
-- by
--   intros v c
--   rw [vDomainDecomp.apply]
--   rw [DomainDecomp.apply]
--   simp
--   rw [foobar]
--   apply congrArg
--   rw [list_vgoal_derive_def]
--   simp
--   rw [vFamily.derive_def]
--   simp
--   induction v with
--   | nil => simp_all
--   | cons h t ih =>
--     simp_all
--     rw [vGoal.pc] at *
--     simp
--     by_cases hc : c ⊨ h.2
--     . simp_all
--       rw [vGoal.derive_pred]
--       simp
--       rw [derive_def_prod]
--       aesop
--     . simp_all


lemma domDecompLiftApply
  {α : Type} [DecidableEq α]  {Φ : FeatModel F}
  {P : α → Prop} :
  isLift (Φ:=Φ) (α := vSet α F × vFamily α F) (β := List (vGSN Φ)) (DomainDecomp P).apply (vDomainDecomp.apply' P)  :=
by
  intros v c
  rw [vDomainDecomp.apply']
  unfold DomainDecomp ; simp only
  rw [DomainDecomp.apply]
  rw [undev_comm]
  apply congrArg
  rw [list_vgoal_derive_def]
  rw [vFamily.derive_def]
  induction v.2 with
  | nil => simp_all
  | cons h t ih =>
    simp only [Prod.mk.eta, List.map_cons, List.filterMap_cons, List.filterMap_map, List.map_map]
    rw [vGoal.pc] at *
    by_cases hc : c ⊨ h.2
    . rw [vGoal.derive_pred]
      rw [derive_def_prod]
      simp only [hc, ↓reduceIte, decide_True, List.filter_cons_of_pos, List.map_cons,
        Function.comp_apply, List.cons.injEq, true_and]
      simp_all only [Prod.mk.eta, List.filterMap_map, List.map_map]
    . simp_all only [Prod.mk.eta, List.filterMap_map, List.map_map, ite_false, decide_False,
      Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]




  -- rw [undevGoals, GSN.undevGoals]
  -- simp
  -- simp only [Prod.mk.eta, List.map_map,vGSN_list_derive_def,mapFilterNil,ne_eq, decide_not, List.map_eq_map]
  -- induction v using Finset.induction_on with
  -- | empty =>
  --   rw [Finset.toList_empty,vFamily.derive_def];
  --   simp only [List.map_nil, List.attach_nil,List.filter_nil, Finset.filter_empty, Finset.image_empty, Finset.toList_empty]
  --   rw [List.filterMap]
  -- | @insert x v h ih =>
  --   rename_i inst Φ_1 α_1 inst_1 inst_2 α_2 inst_3 inst_4
  --   obtain ⟨fst, snd⟩ := x
  --   rw [vFamily.derive_def]

noncomputable def vDomainDecomp  {α : Type} [DecidableEq α] {Φ : FeatModel F} (P : α → Prop) (pc : PC F) : vTemplate' (Set α) (Family α) (vSet α F) (vFamily α F) Φ :=
  {
    parentPC := pc
    parent := invariant P
    prec := λ (s, v) => vComplete_restrict (Φ:=Φ) s v pc
    apply := λ (_,v) => vDomainDecomp.apply P v
  }

-- lemma fingers {s : vSet α F} {v : vFamily α F} {P : α → Prop} {pc : PC F}  :
--   domainDecomp P pc = (lift' domainDecomp (domainDecomp P pc).apply)



lemma domainDecomp_apply {α : Type} [DecidableEq α] {Φ : FeatModel F} {P : α → Prop} {pc : PC F} {s : vSet α F} {f : vFamily α F} :
  (vDomainDecomp P pc (Φ:=Φ)).apply (s, f) = undevGoals (f.map (λ ⟨s',pc'⟩ => vGoal.pred pc' (λ t => ∀ x ∈ t, P x) (Prod.mk s' pc'))) :=
  rfl

namespace foo


theorem vDomDecompValid (P : α → Prop) (pc : PC F) :
  valid' (α := vSet α F) (A := Set α) (Φ := Φ) (vDomainDecomp (α := α) P pc (Φ:=Φ)) :=
by
  intros s f complete c hsat subs
  rw [domainDecomp_apply] at subs
  unfold vDomainDecomp at *
  simp at *
  rw [prod_derive_def] at *
  rw [vGoal.derive_pred, Goal.semantics]
  intros x hx
  simp at subs
  rw [undev_comm] at subs
  rw [GSN.undevGoals_roots_inv] at subs
  rw [list_vgoal_derive_def] at subs
  rw [vGoal.pc] at hsat ; simp at hsat
  rw [vComplete_restrict] at complete
  replace complete := complete c hsat
  replace complete := complete x hx
  cases' complete with T hT
  rw [vFamily.derive_mem_iff] at hT
  rcases hT with ⟨hT,hT'⟩
  cases' hT with t hT
  replace subs := subs (Goal.pred (invariant P) t.1)
  simp only [List.filterMap_map, List.mem_filterMap, Function.comp_apply, ite_some_none_eq_some,
    Prod.exists, forall_exists_index, and_imp] at subs
  apply subs t.1 t.2 (by tauto) (by rw [vGoal.pc]; simp_all)
  simp_all
  . rw [vGoal.derive_pred] ; unfold invariant
    simp
    rw [derive_def_prod]
    simp_all
  . simp_all


theorem vDomDecompValid' (P : α → Prop) (s : vSet α F) (v : vFamily α F) (pc : PC F) :
    [Φ| pc] complete (s,v) →
     vGSN.refines (vGoal.pred (Φ :=Φ) pc (invariant P) s) (vDomainDecomp.apply P v)
 :=
by
    have := vDomDecompValid (Φ := Φ) P pc
    rw [valid'] at this
    replace this := this s v
    apply this

lemma vDomDecompValid'' (P : α → Prop) (pc : PC F) :
    (vDomainDecomp (α := α) P pc (Φ:=Φ)) = (lift' (Φ := Φ) (DomainDecomp P) (vDomainDecomp.apply' P) pc)
 :=
by
  rw [lift', vDomainDecomp, DomainDecomp,]
  simp only [Prod.mk.eta, vTemplate'.mk.injEq, true_and]
  unfold vDomainDecomp.apply' vDomainDecomp.apply vComplete_restrict
  simp only [Prod.mk.eta, true_and]
  funext x
  rw [confInv, eq_iff_iff]
  constructor <;> (intros h c hc ; apply h c hc)


theorem vDomDecompValid''' (P : α → Prop) (pc : PC F) :
    valid' (α := vSet α F) (A := Set α) (Φ := Φ) (vDomainDecomp (α := α) P pc (Φ:=Φ))
 :=
by
  rw [vDomDecompValid'' P]
  apply lift_valid' (DomainDecomp P) ((vDomainDecomp P pc).apply) (domDecompLiftApply (Φ:=Φ) (P:=P)) pc
  exact domainDecompValid


  -- intros s f complete c hsat subs
  -- rw [domainDecomp_apply] at subs
  -- unfold vDomainDecomp at *
  -- simp at *
  -- rw [prod_derive_def] at *
  -- simp only
  -- rw [vGoal.derive_pred, Goal.semantics]
  -- simp
  -- intros x hx
  -- simp at subs
  -- rw [foobar] at subs
  -- rw [GSN.undevGoals_roots_inv] at subs
  -- rw [list_vgoal_derive_def] at subs
  -- rw [vGoal.pc] at hsat ; simp at hsat
  -- rw [vComplete_restrict] at complete
  -- replace complete := complete c hsat
  -- replace complete := complete x hx
  -- cases' complete with T hT
  -- rw [vFamily.derive_mem_iff] at hT
  -- rcases hT with ⟨hT,hT'⟩
  -- cases' hT with t hT
  -- replace subs := subs (Goal.pred (invariant P) t.1)
  -- simp at subs
  -- apply subs t.1 t.2 (by aesop) (by rw [vGoal.pc]; simp_all)
  -- simp_all
  -- . rw [vGoal.derive_pred]
  --   simp
  --   unfold invariant
  --   simp
  --   rw [derive_def_prod]
  --   simp_all
  -- . simp_all











  -- rw [domainDecomp,vGoal.pc] at * ;
  -- simp only [set_idx, Subtype.forall, Prod.mk.eta, List.mem_map,Finset.mem_toList, Prod.exists, forall_exists_index, and_imp] at *
  -- replace complete := complete c hsat
  -- simp only [Subtype.coe_eta] at complete
  -- rw [undevGoals]
  -- simp
  -- rw [Goal.semantics]
  -- simp
  -- simp only [set_idx]
  -- intros k hsatx
  -- rcases complete k hsatx with ⟨T, hT, hT'⟩
  -- have := vFinFamily.derive_mem_iff.mp hT
  -- cases' this with t ht
  -- replace subs := subs (vGoal.pred t.2 (λ t => ∀ x ∈ t, P x) t) t.1 t.2 (by simp [ht.1] )
  -- rw [vGoal.pc] at subs ; simp at subs
  -- replace subs := subs ht.2.2
  -- rw [semantics, vGoal.derive_pred] at subs
  -- simp at subs
  -- apply subs k
  -- rw [← ht.2.1] at hT'
  -- rw [derive_def_prod_fin]
  -- simp [ht.2.2]
  -- exact hT'

-- end Finite

-- variable {α : Type} [DecidableEq α]  {Φ : FeatModel F}

def complete (S : vFinset α F) (V : vFinFamily α F) (Φ : FeatModel F) : Prop :=
  ∀ c : Config Φ,
    ∀ x ∈ S ↓ c,
      ∃ T ∈ V ↓ c, x ∈ T


-- noncomputable
-- def decompose (S : vFinset α F) : vFinFamily α F :=
--   S.toList.map (λ ⟨a,pc⟩ => ⟨{a},pc⟩ )

noncomputable
def explode (S : vFinset α F) : vList (Finset α) F := S.toList.map (λ ⟨a,pc⟩ => ⟨{a},pc⟩ )

noncomputable
 def allPCs (S : vFinset α F) : List (PC F) :=
  (explode S).map Prod.snd

noncomputable
 def aggregate
  (S : vFinset α F) : vList (Finset α) F :=
  let get_singletons : PC F → (Finset (Finset α)) := λ p => ((explode S).filter <| λ ⟨_,pc⟩ => p = pc).toFinset.image (Prod.fst)
  let aggregate : PC F → (Finset α) := λ p => (get_singletons p).sup (. ∪.) ∅
  (allPCs S).map (λ pc => ⟨aggregate pc,pc⟩)


theorem complete_decomp {S : vFinset α F} : complete S (explode S) Φ :=
by
  rw [complete]
  rw [explode]
  simp
  intros c x xmem
  have := vFinset.derive_mem_iff_exist_pc.mp xmem
  use {x}
  simp only [Finset.mem_singleton, and_true]
  rw [vFinFamily.derive_def]
  simp
  cases' this with p hp
  use p
  rw [List.mem_filter]
  simp_all


theorem complete_aggregate [DecidableEq α] {S :vFinset α F} : complete S (aggregate S) Φ :=
by
  rw [complete]
  rw [aggregate]
  simp
  intros c x hx
  rw [@vFinset.derive_mem_iff_exist_pc] at hx
  rcases hx with ⟨a,b, hx⟩
  use (S.image Prod.fst).filter (λ c => ∃ k ∈ S, k.1 = c ∧ k.2 = a)
  simp only [Prod.exists, exists_eq_right_right, exists_eq_right, Finset.mem_filter,
    Finset.mem_image, exists_and_right]
  split_ands
  .
    rw [@vFinFamily.derive_mem_iff]
    simp only [List.mem_map, exists_exists_and_eq_and]
    use a
    rw [allPCs,explode]
    simp
    constructor
    . use x
    . constructor
      .
        ext z
        simp
        simp [Finset.mem_sup]
        aesop

        -- induction S using Finset.induction generalizing x with
        -- | empty =>
        --   simp
        -- | @insert x' s' h' h'' =>
        --    simp only [Finset.mem_insert, Finset.image_insert]
        --    ext x''
        --    simp
        --    constructor
        --    . intro h
        --      simp at h

        --    . admit

      . assumption
  . use a
  . aesop






-- namespace General
-- /-- NOTE: `[DecidableEq (Set α)]` is not generally synthesizable in practice.
--  -- The "easier to use" version is the one for Finsets above.
--  -- We keep this version just for reference, while we develop an alternative setup for sets defined  by decidable predicates -/
-- noncomputable def domainDecomp  {α : Type} [DecidableEq (Set α)]  {Φ : FeatModel F} (P : α → Prop) (pc : PC F) : vTemplate (Set α) (Family α) (vSet α F) (vFamily α F) Φ :=
--   {
--     parentPC := pc
--     parent := λ s => ∀ x ∈ s, P x
--     prec := λ (s, v) => ∀ c : Config Φ, c ⊨ pc → ∀ x ∈ s ↓ c, ∃ T ∈ v ↓ c, x ∈ T
--     apply := λ (_, v) => v.toList.map (λ ⟨s,pc'⟩ => .pred pc' (λ t => ∀ x ∈ t, P x) (Prod.mk s pc') )
--   }

-- lemma domainDecomp_apply {α : Type} [DecidableEq (Set α)]  {Φ : FeatModel F} {P : α → Prop} {pc : PC F} {s : vSet α F} {f : vFamily α F} :
--   (domainDecomp P pc (Φ:=Φ)).apply (s, f) = f.toList.map (λ ⟨s,pc'⟩ => vGoal.pred pc' (λ t => ∀ x ∈ t, P x) (Prod.mk s pc') ) :=
--   rfl

-- theorem domainDecompValid {α : Type} [DecidableEq (Set α)]  {Φ : FeatModel F} (P : α → Prop) (pc : PC F) : valid (domainDecomp P pc (Φ:=Φ)) :=
-- by
--   intros s f complete c hsat subs
--   rw [domainDecomp_apply] at subs
--   rw [domainDecomp,vGoal.pc] at * ;
--   simp only [set_idx, Subtype.forall, Prod.mk.eta, List.mem_map,Finset.mem_toList, Prod.exists, forall_exists_index, and_imp] at *
--   replace complete := complete c hsat
--   simp only [Subtype.coe_eta] at complete
--   rw [semantics,vGoal.derive_pred]
--   simp only [set_idx]
--   intros k hsatx
--   rcases complete k hsatx with ⟨T, hT, hT'⟩
--   have := vFamily.derive_mem_iff.mp hT
--   cases' this with t ht
--   replace subs := subs (vGoal.pred t.2 (λ t => ∀ x ∈ t, P x) t) t.1 t.2 (by simp [ht.1] )
--   rw [vGoal.pc] at subs ; simp at subs
--   replace subs := subs ht.2.2
--   rw [semantics, vGoal.derive_pred] at subs
--   simp at subs
--   apply subs k
--   rw [← ht.2.1] at hT'
--   rw [derive_def_prod]
--   simp [ht.2.2]
--   exact hT'

-- end General
-- end vTemplate
