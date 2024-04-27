
import SPL.Lifting
set_option autoImplicit false

universe u

/- For convenience, we use `Family α` as an alias for `Finset (Set α)` -/
abbrev Family (α : Type u) := Finset (Set α)
abbrev FinFamily (α : Type u) := Finset (Finset α)
/- Our encoding of variational follows the formalization by Shahin: https://github.com/ramyshahin/variability/blob/master/Var/liftedSet.lean -/
namespace SPL

/--
Given a lifted set S and an element x, (S x) denotes the set of configurations in which x is an element of S.
-/
def vSet (α : Type u) (F : Type) : Type u := α → PC F

namespace vSet
variable {F : Type} [FeatureSet F]

variable {α : Type u} [Fintype α] [DecidableEq α]  {Φ : FeatModel F}

@[default_instance]
instance set_derive : Var (vSet α F) (Set α)  Φ :=
    { derive :=  λ s c => λ x ↦ c ⊨ s x}

@[simp]
lemma set_idx {s : vSet α F} {c : Config Φ} {x : α} : x ∈ s ↓ c ↔ c ⊨ s x := by rfl

def union (s₁ s₂ : vSet α F) : vSet α F  := λ x => s₁ x ||| s₂ x

@[reducible]
instance : Union (vSet α F) := ⟨vSet.union⟩

lemma union_def {s t : vSet α F} : s ∪ t = (λ x => s x ||| t x) := rfl

def inter (s₁ s₂ : vSet α F) : vSet α F  := λ x => s₁ x &&& s₂ x

instance : Inter (vSet α F) := ⟨vSet.inter⟩

lemma inter_def {s t : vSet α F} : s ∩  t = (λ x =>  s x &&& t x) := rfl

def diff (s₁ s₂ : vSet α F) : vSet α F := λ x => (s₁ x) &&& ~~~(s₂ x)

instance : SDiff (vSet α F) := ⟨vSet.diff⟩

lemma diff_def {s t : vSet α F} : s \ t = (λ x => s x &&& ~~~ t x) := rfl

lemma lifted_union : isLift₂  (Φ := Φ) (.∪.) (vSet.union (α := α)) :=
by
    intros a b c
    unfold vSet.union ; dsimp only
    ext x
    rw [set_idx, Set.mem_union,set_idx,set_idx, PC.sat_disj]

lemma lifted_inter : isLift₂ (Φ := Φ) (.∩.) (vSet.inter (α := α)) :=
by
    intros a b c
    unfold vSet.inter ; dsimp only
    ext x
    rw [set_idx, Set.mem_inter_iff,set_idx,set_idx, PC.sat_conj]

end vSet

instance {α : Type u} {F : Type} [FeatureSet F] {Φ : FeatModel F} : Var (Set α × PC F) (Set α) Φ :=
  ⟨ λ ⟨s,pc⟩  c => if c ⊨ pc then s else ∅  ⟩

lemma derive_def_prod  {α : Type u} {F : Type} [FeatureSet F] {Φ : FeatModel F} {t : (Set α × PC F)} {c : Config Φ} :
    t ↓ c = if c ⊨ t.2 then t.1 else ∅ := rfl

instance {α : Type u} {F : Type} [FeatureSet F] {Φ : FeatModel F} : Var (Finset α × PC F) (Finset α) Φ :=
  ⟨ λ ⟨s,pc⟩  c => if c ⊨ pc then s else ∅  ⟩

lemma derive_def_prod_fin  {α : Type u} {F : Type} [FeatureSet F] {Φ : FeatModel F} {t : (Finset α × PC F)} {c : Config Φ} :
    t ↓ c = if c ⊨ t.2 then t.1 else ∅ := rfl


-- For finite sets, we can also just enumeratively annotate members.

@[reducible]
def vFinset (α: Type u) (F : Type) [FeatureSet F] := Finset ((α) × PC F)
variable {α : Type u} {F : Type} [DecidableEq α] [FeatureSet F] {Φ : FeatModel F}

namespace vFinset

def derive  (S : vFinset α F) : Config Φ → Finset α :=
  λ c =>
    let filtered := S.filter (λ ⟨_,p⟩ => c ⊨ p)
    filtered.image Prod.fst

instance : Var (vFinset α F) (Finset α) Φ :=
  ⟨derive⟩

-- Coerce an explicit variational finset to variational set using choice
noncomputable def toSet (s : vFinset α F) : vSet α F :=
  λ x =>
    let elems := s.toList
    match elems.find? (λ ⟨k,_⟩ ↦ k=x) with
    | none => ⊥
    | some (_,pc) => pc


-- noncomputable instance : Coe (vFinset α F) (vSet α F) := ⟨toSet⟩

lemma derive_def {S : vFinset α F} {c : Config Φ} : S ↓ c = derive S c := rfl

lemma derive_mem_iff_exist_pc
  {S : vFinset α F} {c : Config Φ} {x : α} :
    x ∈ S ↓ c ↔ ∃ p : PC F, (x,p) ∈ S ∧ c ⊨ p :=
by
  rw [derive_def]
  unfold derive
  simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right]
end vFinset
-- finite families of annotated sets (note : not sets of annotated elements)
abbrev vFamily (α : Type u) (F : Type) [FeatureSet F] := vFinset (Set α) F

namespace vFamily

-- Obviously, [DecidableEq (Set α)] can be constructed in general. This is mostly for illustration.
-- This is why, it comes to e.g., domain decompositions, we use finite sets.
-- There are workarounds obviously, but mostly they are specific to each carrier type α.
-- Another alternative (which we should pursue) is to restrict this variational type to sets over decidable predicates
def derive [DecidableEq (Set α)] (f : vFamily α F) (c : Config Φ) : Family α :=
  let sat_set := f.filter (λ ⟨_,p⟩ => c ⊨ p)
  sat_set.image Prod.fst

instance [DecidableEq (Set α)] : Var (vFamily α F) (Family α) Φ := ⟨derive⟩
lemma derive_def  [DecidableEq (Set α)] {f : vFamily α F} {c : Config Φ} :
  f ↓ c = (f.filter (λ ⟨_,p⟩ => c ⊨ p)).image Prod.fst := rfl

lemma derive_mem_iff  [DecidableEq (Set α)] {f : vFamily α F} {s : Set α} {c : Config Φ} :
  s ∈ f ↓ c ↔ ∃ t ∈ f, t.1 = s ∧ c ⊨ t.2 :=
  by
    constructor
    . intro h
      rw [derive_def] at h
      simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right] at *
      use s
      simp only [true_and] ; exact h
    . intro h
      rw [derive_def]
      simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right]
      rcases h with ⟨t, h1,h2,h3⟩
      use t.2
      simp [h3]
      rw [← h2]
      simp [h1]
end vFamily

abbrev vFinFamily (α : Type u) (F : Type) [FeatureSet F] := vFinset (Finset α) F


namespace vFinFamily

def derive [DecidableEq α] (f : vFinFamily α F) (c : Config Φ) : FinFamily α :=
  let sat_set := f.filter (λ ⟨_,p⟩ => c ⊨ p)
  sat_set.image Prod.fst

instance : Var (vFinFamily α F) (FinFamily α) Φ := ⟨derive⟩

lemma derive_def  [DecidableEq α] {f : vFinFamily α F} {c : Config Φ} :
  f ↓ c = (f.filter (λ ⟨_,p⟩ => c ⊨ p)).image Prod.fst := rfl


lemma derive_mem_iff [DecidableEq α] {f : vFinFamily α F} {s : Finset α} {c : Config Φ} :
  s ∈ f ↓ c ↔ ∃ t ∈ f, t.1 = s ∧ c ⊨ t.2 :=
  by
    constructor
    . intro h
      rw [derive_def] at h
      simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right] at *
      use s
      simp only [true_and] ; exact h
    . intro h
      rw [derive_def]
      simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right]
      rcases h with ⟨t, h1,h2,h3⟩
      use t.2
      simp [h3]
      rw [← h2]
      simp [h1]

end vFinFamily
