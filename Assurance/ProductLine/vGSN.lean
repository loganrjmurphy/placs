import Assurance.ProductLine.vGoal
import Assurance.Product.Properties

set_option autoImplicit false

variable {F : Type} [FeatureSet F]

inductive vGSN (Φ: FeatModel F)
| evd (g : vGoal Φ) : g.varProof → vGSN Φ
| strategy : vGoal Φ → List (vGSN Φ) → vGSN Φ

namespace vGSN

variable {Φ : FeatModel F}

@[induction_eliminator]
def inductionOn
  (motive : vGSN Φ → Prop)
  (evd : ∀ (g : vGoal Φ) (e : g.varProof), motive (vGSN.evd g e))
  (strategy :
     ∀ (g : vGoal Φ) (children : List (vGSN Φ)),
         (∀ (g : vGSN Φ), g ∈ children → motive g)
            → motive (strategy g children))
  : ∀ (G : vGSN Φ), motive G :=
    @vGSN.rec F _ Φ motive (λ gs => ∀ g ∈ gs, motive g) evd strategy
    (List.forall_iff_forall_mem.mp trivial)
    (λ x xs hx ih => by simp only at *; exact List.forall_mem_cons.mpr ⟨hx, ih⟩)

set_option pp.proofs true

def attachedMap
  {α β : Type*}
  (l : List α)
  (f : {x // x ∈ l} → β)
  (P : β → Bool)  : List β :=
  l.attach |> List.filterMap (fun x ↦ if P (f x) then f x else none)

def mapFilterNil (l : List (vGSN Φ)) (f : {x // x ∈ l} → GSN) : List GSN :=
  attachedMap (β := GSN) l f (¬ . = GSN.nil)

theorem aux {α : Type*} {h : α} {t : List α} : h ∈ h::t := (List.mem_cons_self h t)
theorem aux' {α : Type*} {h : α} {t : List α} (x : { x // x ∈ t }) : ↑x ∈ h :: t :=  by apply List.mem_cons_of_mem ; apply x.property

open List


def myMapFn
    {α β : Type}
    (l : List α)
    (f : {x // x ∈ l} → β)
    (P : β → Bool)  : List β :=
  l.attach |> List.filterMap (fun x ↦ if P (f x) then f x else none)

theorem filterMap_id_map {α β} (f : α → Option β) (l : List α) :
    filterMap id (map f l) = filterMap f l :=
  filterMap_map ..

theorem attach_map_cons_pos
    {α β : Type*}
    (h : α)
    (t : List α)
    (f : {x // x ∈ h::t} → β)
    (P : β → Bool)
    (h': P (f ⟨h, aux⟩)) :
    attachedMap (h::t) f P =
    f ⟨h,aux⟩ :: attachedMap t (λ x => f ⟨x, aux' x⟩) P := by
  simp_rw [attachedMap, attach, attachWith, pmap, filterMap_cons, h']
  simp (config := {singlePass := true}) only [← filterMap_id_map]
  simp_rw [map_pmap]
  congr 2
  exact pmap_congr t fun a _ h₁ => congrFun rfl

theorem attach_map_cons_neg
    {α β : Type*}
    (h : α)
    (t : List α)
    (f : {x // x ∈ h::t} → β)
    (P : β → Bool)
    (h': ¬ P (f ⟨h, aux⟩)) :
    attachedMap (h::t) f P =
    attachedMap t (λ x => f ⟨x, aux' x⟩) P := by
  simp_rw [attachedMap, attach, attachWith, pmap, filterMap_cons, h']
  simp (config := {singlePass := true}) only [← filterMap_id_map]
  simp_rw [map_pmap]
  congr 1
  simp only [id_eq]
  apply pmap_congr
  simp only [mem_cons, implies_true]


def mapFilter_cons_pos
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

def mapFilter_cons_neg
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


universe u v

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
    rw [mem_filterMap] at *
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
    rw [mem_filterMap] at *
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

end vGSN
