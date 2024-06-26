import Assurance.vGSN.Defs
import Var

set_option autoImplicit false


namespace vGSN
variable {F : Type} [FeatureSet F] {Φ : FeatModel F}

lemma mapFilter_cons_pos
  (h : vGSN Φ)
  (t : List (vGSN Φ))
  {hh : h ∈ h::t}
  (f : {x // x ∈ h::t} → GSN)
  (h': ¬ f ⟨h,hh⟩ = GSN.nil)
  :
  (mapFilterNil (h::t) f) =
    (f ⟨h,hh⟩ :: mapFilterNil t (λ x => f ⟨x, by aesop⟩ )) :=
    by
    rw [mapFilterNil]
    rw [mapFilterNil]
    rw [attach_map_cons_pos]
    simp_all

lemma mapFilter_cons_neg
  (h : vGSN Φ)
  (t : List (vGSN Φ))
  {hh : h ∈ h::t}
  (f : {x // x ∈ h::t} → GSN)
  (h': f ⟨h,hh⟩ = GSN.nil)
  :
  (mapFilterNil (h::t) f) =
    (mapFilterNil t (λ x => f ⟨x, by aesop⟩ )) :=
    by
    rw [mapFilterNil]
    rw [mapFilterNil]
    rw [attach_map_cons_neg]
    simp_all


@[reducible]
def derive (c : Config Φ) : vGSN Φ → GSN
| .evd g e =>
  if h:c ⊨ g.pc then .evd (g ↓ c) (e c h) else .nil
| strategy g children=>
  if c ⊨ g.pc then
    GSN.strategy (g ↓ c) (mapFilterNil children (λ ⟨x,_⟩ ↦
      derive c x))
  else .nil
decreasing_by
  simp_wf
  cases x <;> (rename_i h; have := List.sizeOf_lt_of_mem h; omega)

instance : Var (vGSN Φ) (GSN) Φ := ⟨λ x c => vGSN.derive c x⟩
lemma derive_def {g : vGSN Φ} {c : Config Φ} : g ↓ c = g.derive c := rfl

instance : Var (List (vGSN Φ)) (List GSN) Φ := ⟨λ l c => mapFilterNil l (λ ⟨x,_⟩ ↦ x ↓ c)⟩
theorem vGSN_list_derive_def {l : List (vGSN Φ)} {c : Config Φ} : l ↓ c = (mapFilterNil l (λ ⟨x,_⟩ ↦ x  ↓ c)) := rfl

def root : vGSN Φ → vGoal Φ
| .evd g _ => g
| strategy g _ => g

lemma evd_root {g : vGoal Φ} {e : g.varProof} : root (.evd g  e) = g := rfl
lemma strategy_root {g : vGoal Φ} {l : List (vGSN Φ)} : root (.strategy g l) = g := rfl

lemma derive_evd_sat_iff {c : Config Φ} {g : vGoal Φ} {e : g.varProof}:
   (c ⊨ g.pc) ↔ (vGSN.evd g e) ↓ c ≠ GSN.nil := by
  rw [derive_def,derive]; by_cases hc : c ⊨ g.pc <;> simp [hc]

lemma derive_strat_sat_iff {c : Config Φ} {g : vGoal Φ} {l : List (vGSN Φ)}  : c ⊨ g.pc ↔
  ((vGSN.strategy g l) ↓ c) ≠ .nil :=
  by rw [derive_def,derive]
     by_cases hc : c ⊨ g.pc <;> (simp [hc])

lemma derive_sat_iff_ne_nil {c : Config Φ} {g : vGSN Φ} : c ⊨ g.root.pc ↔ (g ↓ c) ≠ .nil :=
  by cases g with
     | evd g e => exact derive_evd_sat_iff
     | strategy g gs => exact derive_strat_sat_iff

lemma derive_evd_of_sat
  {c : Config Φ} {g : vGoal Φ} {e : g.varProof} (h : c ⊨ g.pc) :
    (vGSN.evd g e) ↓ c = (GSN.evd (g ↓ c) (e c h)) :=
    by rw [derive_def,derive]
       by_cases hc : c ⊨ g.pc <;> (simp [hc]) ; contradiction

lemma derive_strat_of_sat
  {c : Config Φ} {g : vGoal Φ} {l : List (vGSN Φ)} (h : c ⊨ g.pc)  :
     ((vGSN.strategy g l) ↓ c) = (GSN.strategy (g ↓ c) (l ↓ c)) :=
    by
      rw [derive_def,derive]
      simp only [h, ↓reduceIte, GSN.strategy.injEq, true_and]
      rfl

lemma root_derive_eq_root {c : Config Φ} {A : vGSN Φ} {h : c ⊨ A.root.pc} :
  ∃ h' : (A ↓ c) ≠ .nil, (A ↓ c).root h' = (A.root) ↓ c :=
by
  cases A with
  | evd g e =>
     rw [vGSN.evd_root] at h
     use (derive_evd_sat_iff (c:=c) (g:= g) (e:=e)).mp h
     simp only [vGSN.evd_root]
     have := derive_evd_of_sat (c := c) (g:=g) (e:=e) h
     simp only [this,GSN.evd_root]
  | strategy g l =>
    rw [vGSN.strategy_root] at h
    use (derive_strat_sat_iff (c:=c) (g:=g) (l:=l)).mp h
    have := derive_strat_of_sat (c:=c) (g:=g) (l:=l) h
    simp only [this, GSN.strategy_root]
    rfl

def roots (l : List (vGSN Φ)) : List (vGoal Φ) :=
  root <$> l

lemma mem_roots_iff {g : vGoal Φ} {l : List (vGSN Φ)} :
  g ∈ roots l ↔ ∃ k ∈ l, root k = g :=
  by rw [roots,List.map_eq_map,List.mem_map]

lemma derive_list_gsn_ne_nil_iff {l : List (vGSN Φ)} {c : Config Φ} :
  ¬l↓c = [] ↔ ∃ x ∈ l, ¬ x ↓ c = GSN.nil :=
by
  rw [vGSN_list_derive_def, mapFilterNil]
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [List.mem_filterMap, List.mem_attach, true_and, Subtype.exists, exists_prop, not_exists,
    not_and, not_forall, Classical.not_imp, not_not]
  constructor
  . intro h
    cases' h with x hx
    rw [attachedMap] at *
    rw [List.mem_filterMap] at *
    cases' hx with hx hxx
    simp_all
    by_cases hc : hx.1 ↓ c = GSN.nil
    . simp [hc] at hxx
    . simp [hc] at hxx
      use hx
      aesop
  . intro h
    cases' h with x hx
    use (x ↓ c)
    rw [attachedMap] at *
    rw [List.mem_filterMap] at *
    use ⟨x,hx.1⟩
    simp_all


theorem derive_mem_derive
  {c : Config Φ} (gs : List (vGSN Φ)) (g' : vGSN Φ)
  (hg' : g' ∈ gs) (hc : c ⊨ g'.root.pc) : g'↓c ∈ gs↓c :=
  by
    rw [vGSN_list_derive_def]; simp
    rw [mapFilterNil]
    rw [attachedMap]
    rw [List.mem_filterMap]
    simp
    use g'
    constructor
    . assumption
    . have := derive_sat_iff_ne_nil (c:=c) (g:=g')
      replace this := this.mp hc
      simp [this]

def subtreesDeveloped (g : vGoal Φ) (l : List (vGSN Φ)) : Prop :=
  [Φ| g.pc] (. ≠ []) l

lemma subtreesDeveloped_iff_forall_not_nil {g : vGoal Φ} {l : List (vGSN Φ)} :
  subtreesDeveloped g l ↔
  ∀ c : Config Φ, c ⊨ g.pc → ∃ A : vGSN Φ, A ∈ l ∧ c ⊨ A.root.pc :=
by
  rw [subtreesDeveloped]
  constructor <;> (intros h c hc ; replace h := h c hc )
  . simp only [ne_eq] at h
    rw [derive_list_gsn_ne_nil_iff] at h
    rcases h with ⟨w, hw1, hw2⟩
    use w
    exact ⟨hw1, derive_sat_iff_ne_nil.mpr hw2⟩
  . rw [ne_eq,derive_list_gsn_ne_nil_iff]
    rcases h with ⟨w, hw1, hw2⟩
    use w
    exact ⟨hw1, derive_sat_iff_ne_nil.mp hw2⟩


def recStrategyPred (P : vGoal Φ → List (vGSN Φ) → Prop) : vGSN Φ → Prop
| .evd _ _ => True
| .strategy parent children => P parent children ∧ children.attach.Forall (λ ⟨x,_⟩ => recStrategyPred P x)

lemma recStrategyPred_evd {P : vGoal Φ → List (vGSN Φ) → Prop} {g : vGoal Φ} {e : g.varProof} : recStrategyPred P (.evd g e) :=
  by rw [recStrategyPred] ; trivial

lemma recStrategyPred_strat {P : vGoal Φ → List (vGSN Φ) → Prop} {g : vGoal Φ} {l : List (vGSN Φ)} :
  recStrategyPred P (.strategy g l) ↔ P g l ∧ l.attach.Forall (λ ⟨x,_⟩ => recStrategyPred P x) :=
  by rw [recStrategyPred]

def refines (g : vGoal Φ) (l : List (vGSN Φ)) : Prop :=
  [Φ| g.pc] GSN.refines (g,l)

def developed : vGSN Φ → Prop := recStrategyPred subtreesDeveloped

def deductive : vGSN Φ → Prop := recStrategyPred refines

lemma deductive_evd {g : vGoal Φ} {e : g.varProof} : deductive (.evd g  e) := recStrategyPred_evd

lemma deductive_strat {g : vGoal Φ} {l : List (vGSN Φ)} : deductive (.strategy g l) ↔ refines g l ∧ ∀ g' ∈ l, deductive g' :=
  by
    have := recStrategyPred_strat (P:= (λ g gs => refines g  gs)) (g:=g) (l:=l)
    rw [deductive,this] ; clear this
    rw [List.forall_iff_forall_mem]
    simp only [List.mem_attach, true_implies, Subtype.forall, implies_true]

def wf_strat_pred (g : vGoal Φ) (children : List (vGSN Φ)) : Prop := (∀ g' ∈ children, ⦃g'.root.pc⦄ ⊆ ⦃(g.pc : FeatExpr F)⦄)

def wf_strat_def {g : vGoal Φ} {children : List (vGSN Φ)} : wf_strat_pred g children ↔  (∀ g' ∈ children, ⦃g'.root.pc⦄ ⊆ ⦃(g.pc : FeatExpr F)⦄) := Iff.rfl

def wf : vGSN Φ → Prop := recStrategyPred wf_strat_pred

lemma wf_evd {g : vGoal Φ} {e : g.varProof} : wf (.evd g e) := recStrategyPred_evd

lemma wf_strat {g : vGoal Φ} {l : List (vGSN Φ)} :
   wf (.strategy g  l) ↔ (wf_strat_pred g l) ∧ ∀ g' ∈ l, wf g' :=
  by
    have := recStrategyPred_strat (P:= wf_strat_pred) (g:=g) (l:=l)
    rw [wf,this] ; clear this
    simp only [and_congr_right_iff, List.forall_iff_forall_mem]
    simp only [List.mem_attach, true_implies, Subtype.forall, implies_true]

lemma subgoal_wf {g : vGoal Φ} {l : List (vGSN Φ)} (h: wf (.strategy g l)) (g' : vGSN Φ) (hmem : g' ∈ l) : wf g' :=
  by rw [wf_strat] at h
     exact h.2 g' hmem

theorem derived_subchildren_deductive
  {c : Config Φ} {g : vGoal Φ} {gs : List (vGSN Φ)}
  (h : (vGSN.strategy g gs).deductive) (hc : c⊨ g.pc) : (∀ g' ∈ GSN.roots (gs↓c), ⟦g'⟧) → ⟦g↓c⟧ :=
 by intro subs
    rw [deductive_strat] at h
    cases' h with href hsubs
    replace href := href c hc
    rw [prod_derive_def,GSN.refines_def] at href ; simp only at href
    apply href ; clear href
    intros g' hmem
    replace subs := subs g' hmem
    apply subs

theorem varProof_of_deductive {A : vGSN Φ} :
  vGSN.deductive A → [Φ| A.root.pc] GSN.deductive A :=
by
  intros h c hc
  induction A with
  | evd g e =>
    rw [evd_root] at hc
    rw [derive_evd_of_sat (g:= g) (e:=e) (c:=c) hc]
    exact GSN.evd_deductive
  | strategy g gs ih =>
    rw [derive_strat_of_sat (g:=g) (l:=gs) (c:=c) hc]
    rw [GSN.strat_deductive_iff]
    constructor
    . exact derived_subchildren_deductive h hc
    . intros g' hg'
      rw [vGSN_list_derive_def, mapFilterNil,attachedMap,List.mem_filterMap] at hg'
      simp only [List.map_eq_map, List.mem_map, List.mem_attach, Subtype.exists,exists_prop,true_and] at hg'

      rcases hg' with ⟨g'', h1,h2⟩
      have : g'' ↓ c ≠ GSN.nil :=
        by by_contra hc'
           simp [hc'] at h2

      have deductive'' : g''.deductive  :=
        by rw [deductive_strat] at h
           apply h.2 g'' h1
      have sat'' : c⊨g''.root.pc :=
        by rw [derive_sat_iff_ne_nil (g:= g'') (c:=c)]
           exact this
      simp [this] at h2
      rw [← h2]
      apply ih g'' h1 deductive'' sat''

theorem deductive_of_varProof {A : vGSN Φ} (wfh : wf A) :
  [Φ| A.root.pc] GSN.deductive A → vGSN.deductive A :=
by
  intro h
  induction A with
  | evd g e => exact deductive_evd
  | strategy g gs ih =>
    rw [strategy_root] at h
    rw [deductive_strat]
    constructor
    . rw [refines]
      intros c hc
      replace h := h c hc
      rw [derive_strat_of_sat (h:= hc), GSN.deductive] at h
      rw [prod_derive_def]
      simp only [h.1]
    . intros g' hg'
      have wf' : wf g' :=
        by rw [wf_strat] at wfh
           exact wfh.2 g' hg'
      apply ih g' hg' wf'
      intros c hc
      have hc' : c ⊨ g.pc :=
        by rw [wf_strat,wf_strat_pred] at wfh
           exact wfh.1 g' hg' hc
      have := h c hc'
      rw [derive_strat_of_sat (h:=hc'),GSN.deductive] at this
      simp only at this
      replace this := this.2
      rw [List.forall_iff_forall_mem] at this
      replace this := this ⟨g'↓ c, derive_mem_derive gs g' hg' hc⟩
      apply this
      apply List.mem_attach

end vGSN
