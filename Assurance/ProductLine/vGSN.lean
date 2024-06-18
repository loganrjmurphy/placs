import Var
import Assurance.Product.GSN
set_option autoImplicit false

variable {F : Type} [FeatureSet F]

inductive vGoal (Φ : FeatModel F)
| atom (pc : PC F) (p : Prop) : vGoal Φ
| pred {A α : Type} [Var α A Φ] (pc : PC F)  (P : A → Prop) (x : α) : vGoal Φ

variable {Φ : FeatModel F}

namespace vGoal

def pc : vGoal Φ → PC F
| vGoal.atom pc _ => pc
| vGoal.pred pc _ _ => pc


def vSemantics : vGoal Φ → Config Φ → Prop
| vGoal.atom _ p => λ _ => p
| vGoal.pred _ P x => λ c => P (x ↓ c)

def asGoal : vGoal Φ → Config Φ → Goal
| vGoal.atom _ p => λ _ => .atom p
| vGoal.pred _ P x => λ c => .pred P (x ↓ c)

instance : Var (vGoal Φ) Goal Φ := ⟨asGoal⟩

lemma derive_atom {A α : Type} [Var α A Φ] {pc : PC F}  {P : Prop}  {c : Config Φ} :
  vGoal.atom (Φ:=Φ) pc P ↓ c = Goal.atom P := rfl


lemma derive_pred {A α : Type} [Var α A Φ] {pc : PC F}  {P : A → Prop} {x : α} {c : Config Φ} :
  vGoal.pred (Φ:=Φ) pc P x ↓ c = Goal.pred P (x ↓ c) := rfl

end vGoal

inductive vGSN (Φ: FeatModel F)
| evd (g : vGoal Φ) : (∀ (c : Config Φ), c ⊨ g.pc → ⟦g ↓ c⟧) → vGSN Φ
| strategy : vGoal Φ → List (vGSN Φ) → vGSN Φ

namespace vGSN

abbrev Evd (g : vGoal Φ) := ∀ (c : Config Φ), c ⊨ g.pc → ⟦g ↓ c⟧
scoped infix:80 "⇐" => strategy
scoped infix:80 "↼" => vGSN.evd
scoped infix:81 "⬝" => vGoal.pred

/-- Handwritten induction principle for vGSN trees to simplify proofs about nested inductive trees. To be replaced by more systematic methods -/
def inductionOn
  (motive : vGSN Φ → Prop)
  (evd : ∀ (g : vGoal Φ) (e : Evd g), motive (vGSN.evd g e))
  (strategy :
     ∀ (g : vGoal Φ) (children : List (vGSN Φ)),
         (∀ (g : vGSN Φ), g ∈ children → motive g)
            → motive (strategy g children))
  : ∀ (G : vGSN Φ), motive G :=
    @vGSN.rec F _ Φ motive (λ gs => ∀ g ∈ gs, motive g) evd strategy
    (List.forall_iff_forall_mem.mp trivial)
    (λ x xs hx ih => by simp only at *; exact List.forall_mem_cons.mpr ⟨hx, ih⟩)

def derive (c : Config Φ) : vGSN Φ → GSN
| .evd g e =>
  if h:c ⊨ g.pc then .evd (g ↓ c) (e c h) else .nil
| strategy g children=>
  if c ⊨ g.pc then
    (λ ⟨x,_⟩  => derive c x) <$> children.attach |> List.filter GSN.nnil |> .strategy (g ↓ c)
  else .nil
decreasing_by
  simp_wf
  cases x <;> (rename_i h; have := List.sizeOf_lt_of_mem h; omega)

instance : Var (vGSN Φ) (GSN) Φ := ⟨λ x c => vGSN.derive c x⟩



def root : vGSN Φ → vGoal Φ
| .evd g _ => g
| strategy g _ => g

lemma root_evd {g : vGoal Φ} {e : Evd g} : root (g ↼ e) = g := rfl
lemma root_decomp {g : vGoal Φ} {l : List (vGSN Φ)} : root (g ⇐ l) = g := rfl


lemma derive_def {g : vGSN Φ} {c : Config Φ} : g ↓ c = g.derive c := rfl

lemma derive_evd_pos {c : Config Φ} {g : vGoal Φ} {e : Evd g} {h  : c ⊨ g.pc} : (g ↼ e) ↓ c = GSN.evd (g ↓ c) (e c h) := by rw [derive_def,derive]; simp only [h, reduceDite]
lemma derive_evd_neg {c : Config Φ} {g : vGoal Φ} {e : Evd g} {h  : ¬ c ⊨ g.pc} : (g ↼ e) ↓ c = GSN.nil := by rw [derive_def,derive]; simp only [h, reduceDite]

lemma derive_decomp_pos {c : Config Φ} {g : vGoal Φ} {l : List (vGSN Φ)}  : c ⊨ g.pc ↔
  (g ⇐ l) ↓ c = GSN.strategy (g ↓ c) ((λ ⟨x,_⟩  => derive c x) <$> l.attach |> List.filter GSN.nnil) :=
  by rw [derive_def,derive]; simp only [List.map_eq_map, ite_eq_left_iff, imp_false, not_not]

lemma derive_decomp_nnil_iff {c : Config Φ} {g : vGoal Φ} {l : List (vGSN Φ)}  : c ⊨ g.pc ↔
  GSN.nnil ((g ⇐ l) ↓ c) :=
  by rw [derive_def,derive,List.map_eq_map] ;
     by_cases hc : c ⊨ g.pc <;> (simp [hc])

lemma derive_nnil_iff {c : Config Φ} {A : vGSN Φ} : (A ↓ c).nnil ↔ c ⊨ A.root.pc :=
  by
    cases A with
    | evd g e =>
      rw [vGSN.root_evd]
      by_cases hc : c ⊨ g.pc <;> simp [hc]
      . rwa [derive_evd_pos]
      . rwa [derive_evd_neg]
    | strategy g l => rw [vGSN.root_decomp,derive_decomp_nnil_iff]


lemma derive_decomp_neg {c : Config Φ} {g : vGoal Φ} {l : List (vGSN Φ)} :  ¬ c ⊨ g.pc ↔
  (g ⇐ l) ↓ c = GSN.nil:=
  by rw [derive_def,derive]; simp only [List.map_eq_map, ite_eq_right_iff, imp_false];

lemma derive_evd_true {c : Config Φ} {g : vGoal Φ} {e : Evd g}  : ((g ↼ e) ↓ c).nnil = true ↔ c ⊨ g.pc :=
  by rw [derive_def,derive]
     constructor
     . intro h
       by_cases hc: c ⊨ g.pc
       . exact hc
       . simp_all only [dite_false]
     . intro h ; simp only [h, reduceDite]

lemma derive_evd_false {c : Config Φ} {g : vGoal Φ} {e : Evd g}  : ((g ↼ e) ↓ c).nnil = false ↔ ¬ c ⊨ g.pc :=
  by have := Iff.not <| derive_evd_true (g:=g) (e:= e) (c:=c)
     simp_all only [Bool.not_eq_true]

lemma root_derive_eq_root {c : Config Φ} {A : vGSN Φ} {h : c ⊨ A.root.pc} : ∃ h' : (A ↓ c).nnil, (A ↓ c).root h' = (A.root) ↓ c :=
by
  cases A with
  | evd g e =>
     rw [vGSN.root_evd] at h
     use (derive_evd_true (e:=e)).mpr h
     simp only [vGSN.root_evd,vGSN.derive_evd_pos (e:=e) (h:=h),GSN.root_evd]
  | strategy g l =>
    rw [vGSN.root_decomp] at h
    use (derive_decomp_nnil_iff (c:=c) (g:=g) (l:=l)).mp h
    simp only [vGSN.root_decomp,(vGSN.derive_decomp_pos (l:=l)).mp h,GSN.root_decomp]




def roots (l : List (vGSN Φ)) : List (vGoal Φ) :=
  root <$> l

lemma mem_roots_iff {g : vGoal Φ} {l : List (vGSN Φ)} : g ∈ roots l ↔ ∃ k ∈ l, root k = g :=
  by rw [roots,List.map_eq_map,List.mem_map]


def all_configs_supported (g : vGoal Φ) (l : List (vGSN Φ)) : Prop :=
  ∀ c : Config Φ, c ⊨ g.pc →
    (l.map (derive c) |> List.filter GSN.nnil) ≠ []

lemma all_configs_supported_iff_forall_exists {g : vGoal Φ} {l : List (vGSN Φ)} :
  all_configs_supported g l ↔
  ∀ c : Config Φ, c ⊨ g.pc → ∃ A : vGSN Φ, A ∈ l ∧ c ⊨ A.root.pc :=
by
  rw [all_configs_supported]
  constructor <;> (intros h c hsat ; replace h := h c hsat )
  . simp only [ne_eq, List.filter_eq_nil,List.mem_map, Bool.not_eq_true, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, Bool.not_eq_false, exists_prop] at h
    cases' h with A hA ; use A
    simp only [hA, true_and]
    cases A with
      | evd g' e => rw [vGSN.root_evd] ;  rw [← derive_def,vGSN.derive_evd_true] at hA ; exact hA.2
      | strategy g' l' => rw [vGSN.root_decomp] ; rw [← derive_def, ← vGSN.derive_decomp_nnil_iff] at hA; exact hA.2
  . cases' h with A hA
    simp only [ne_eq,List.filter_eq_nil,List.mem_map, Bool.not_eq_true, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, Bool.not_eq_false, exists_prop]
    use A ;  simp only [hA, true_and]
    . cases A with
      | evd g' e => rw [vGSN.root_evd] at hA ; rw [← derive_def,vGSN.derive_evd_true] ; exact hA.2
      | strategy g' l' => rw [vGSN.root_decomp] at hA ; rw [← derive_def, ← vGSN.derive_decomp_nnil_iff] ; exact hA.2



def refines (g : vGoal Φ) (l : List (vGoal Φ)) : Prop :=
  ∀ c : Config Φ, c ⊨ g.pc →
    (∀ g ∈ l, c ⊨ g.pc → ⟦g ↓c⟧) → ⟦g ↓ c⟧

def supported : vGSN Φ → Prop
| .evd _ _ => True
| strategy g children =>
      all_configs_supported g children ∧
      children.attach.Forall (λ ⟨x,_⟩ => supported x)

def deductive : vGSN Φ → Prop
| .evd _ _ => True
| strategy g children =>
      refines g (roots children) ∧
      children.attach.Forall (λ ⟨x,_⟩ => deductive x)

lemma deductive_evd {g : vGoal Φ} {e : Evd g} : deductive (g ↼ e) := by rw [deductive]; trivial
lemma deductive_evd_eq {g : vGoal Φ} {e : Evd g} : deductive (g ↼ e) = True := by rw [deductive]

lemma deductive_decomp {g : vGoal Φ} {l : List (vGSN Φ)} : deductive (g ⇐ l) ↔ refines g (roots l) ∧ ∀ g' ∈ l, deductive g' :=
by
  rw [deductive] ; simp only [and_congr_right_iff] ; intros
  rw [List.forall_iff_forall_mem]
  simp only [List.mem_attach, forall_true_left, Subtype.forall]

def wf : vGSN Φ → Prop
| .evd _ _ => True
| strategy g children =>
  (∀ g' ∈ children, ⦃g'.root.pc⦄ ⊆ ⦃g.pc⦄) ∧ children.attach.Forall (λ ⟨x,_⟩ => wf x)


lemma wf_evd {g : vGoal Φ} {e : Evd g} : wf (g ↼ e) = True := by rw [wf]
lemma wf_strat {g : vGoal Φ} {l : List (vGSN Φ)} :
   wf (g ⇐ l) ↔ (∀ g' ∈ l, ⦃g'.root.pc⦄ ⊆ ⦃g.pc⦄) ∧ ∀ g' ∈ l, wf g' :=
    by rw [wf] ; simp only [and_congr_right_iff]
       intros
       rw [List.forall_iff_forall_mem]
       simp only [List.mem_attach, forall_true_left, Subtype.forall]

lemma subgoal_wf {g : vGoal Φ} {l : List (vGSN Φ)} (h: wf (g ⇐ l)) (g' : vGSN Φ) (hmem : g' ∈ l) : wf g' :=
  by rw [wf_strat] at h
     exact h.2 g' hmem

theorem helper_1 (g : vGoal Φ) (l : List (vGSN Φ))
  (ih : ∀ g ∈ l, g.deductive ↔ ∀ (c : Config Φ), c⊨g.root.pc → (g↓c).deductive) :
  (refines g (roots l) ∧ ∀ g' ∈ l, g'.deductive) → ∀ (c : Config Φ), c⊨g.pc → ((g⇐l)↓c).deductive :=
by
  intros h c hsat
  cases' h with refines children
  rw [vGSN.derive_decomp_pos.mp hsat, List.map_eq_map, GSN.deductive_decomp]
  constructor
  . intros subgoals
    rw [vGSN.refines] at refines
    apply refines c hsat
    intros g' hg' hsat'
    apply subgoals (g' ↓ c)
    rw [GSN.roots, List.reduceOption_mem_iff,List.mem_map] ; rw [roots,List.map_eq_map,List.mem_map] at hg'
    rcases hg' with ⟨A, ⟨h₁,h₂⟩⟩
    use (A ↓ c)
    simp only [List.mem_filter, List.mem_map,List.mem_attach, true_and, Subtype.exists, exists_prop]
    split_ands
    . use A ; rw [derive_def] ; simp only [h₁,true_and]
    . rwa [derive_nnil_iff,h₂]
    . rw [GSN.root_option_elim]
      rw [← h₂] at hsat'
      have:= root_derive_eq_root (h:=hsat')
      cases' this with h h'
      use h
      rw [h',h₂]
  . intros A' memA'
    rw [List.mem_filter,List.mem_map] at memA'
    rcases memA' with ⟨⟨⟨A,memA⟩,hA⟩,hA'⟩ ; simp at hA
    rw [← derive_def] at hA ; rw [← hA]
    apply Iff.mp <| ih A memA
    . exact children A memA
    . rw [← hA] at hA'
      exact Iff.mp (derive_nnil_iff (A:=A) (c:=c)) hA'

-- Todo : modularize. And push most of the List rewriting stuff into lemmas
theorem deductive_config_invariant {A : vGSN Φ} {wfh : wf A} :
  deductive A ↔ ∀ c : Config Φ, c ⊨ A.root.pc → (A ↓ c).deductive :=
by
  induction A using vGSN.inductionOn with
  | evd g e =>
    rw [vGSN.deductive_evd_eq, true_iff, vGSN.root_evd]
    intros c hsat
    rw [vGSN.derive_evd_pos (h:=hsat)]
    exact GSN.deductive_evd
  | strategy g l ih =>
    rw [vGSN.deductive_decomp, vGSN.root_decomp]
    constructor
    . exact vGSN.helper_1 (Φ:=Φ) g l (λ g' h => (ih (wfh := subgoal_wf wfh g' h) h))
    . intros h
      constructor
      . intros c hsat subgoals
        obtain h := h c hsat
        rw [vGSN.derive_decomp_pos (l:=l).mp hsat,List.map_eq_map, GSN.deductive_decomp] at h
        cases' h with refines children
        apply refines
        intros g' hg'
        rw [GSN.roots, List.reduceOption_mem_iff, List.mem_map] at hg'
        cases' hg' with A hA
        rw [List.mem_filter, List.mem_map] at hA
        rcases hA with ⟨⟨⟨⟨A',h₁⟩,h₂⟩,h₃⟩, hA⟩ ; simp only [List.mem_attach,true_and] at h₂
        rw [GSN.root_option_elim] at hA
        cases' hA with hnnil hA ; rw [← hA]
        simp_all only [derive_def (c:=c) (g:=A')]
        rw [← hA]
        have first : A = A' ↓ c := by rw [derive_def]; symm; exact h₂
        have : GSN.root A hnnil = (vGSN.root A' ↓ c) :=
          by simp [first]
             have:= root_derive_eq_root (A:=A') (c:= c) (h:= by have := derive_nnil_iff (c:=c) (A:=A'); apply this.mp; rwa [← first])
             cases' this with h' this
             rw [this]
        rw [this]
        apply subgoals A'.root
        rw [roots, List.map_eq_map, List.mem_map]
        use A'
        exact derive_nnil_iff.mp (by rw [← hnnil] ; rw [derive_def] ; rw [h₂])
      . intros A memA'
        cases A with
        | evd g' e => exact vGSN.deductive_evd
        | strategy g' l' =>
          rw [wf_strat] at wfh
          cases' wfh with rootwf childrenwf
          apply Iff.mpr (ih (g' ⇐ l') memA')
          . intros c hsat
            rw [root_decomp] at hsat
            have : c ⊨ g.pc := by apply rootwf (g' ⇐ l') memA' ; rwa [root_decomp]
            replace h := h c this
            rw [(vGSN.derive_decomp_pos (c:=c) (g:=g) (l:=l)).mp this, GSN.deductive_decomp] at h
            simp only at h
            apply h.2 ((g' ⇐ l') ↓ c)
            rw [List.mem_filter,List.map_eq_map,List.mem_map]
            constructor
            . use ⟨(g' ⇐ l'),memA'⟩ ; simp [derive_def]
            . rwa [derive_nnil_iff, root_decomp]
          . exact childrenwf (g' ⇐ l') memA'

end vGSN
