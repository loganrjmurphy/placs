import Assurance.Product.GSN

namespace GSN

@[reducible]
def supported : GSN → Bool
| .nil => False
| .evd _ _ => True
| .strategy _ [] => False
| .strategy _ (h::t) => (h::t).attach.all (λ ⟨x,_ ⟩ => supported x)

@[simp]
lemma supported_nil : supported .nil = false := rfl

@[simp]
lemma supported_evd {g : Goal} {h : ⟦g⟧} : supported (.evd g h) = true := by rw [supported]; trivial

@[simp]
lemma supported_empty {g : Goal}  : supported (.strategy g []) = false := rfl

@[simp]
lemma supported_cons {g : Goal} {l : List GSN} : supported (.strategy g l) ↔ l ≠ [] ∧ ∀ x ∈ l, supported x :=
  by cases l <;> rw [supported] <;> simp


def refines (strat : Goal × List GSN) : Prop :=
  let children := roots strat.snd
  (∀ g' ∈ children, ⟦g'⟧) → ⟦strat.fst⟧

@[simp]
def refines_def {g : Goal} {l : List GSN} : refines (g,l) ↔ (∀ g' ∈ roots l, ⟦g'⟧) → ⟦g⟧ := Iff.rfl

def deductive : GSN → Prop
| .nil => False
| .evd _ _ => True
| .strategy g children => refines (g, children) ∧ children.attach.Forall (λ ⟨x,_⟩ => deductive x)

lemma not_deductive_nil : ¬ GSN.nil.deductive := λ h => by rwa [deductive] at h

lemma evd_deductive {g : Goal} {h : ⟦g⟧} : (GSN.evd g h).deductive := by rw [deductive]; trivial

@[simp]
lemma strat_deductive_iff {g : Goal} {l : List GSN} : (GSN.strategy g l).deductive ↔ ((∀ g' ∈ (roots l), ⟦g'⟧) → ⟦g⟧) ∧ ∀ x ∈ l, deductive x :=
  by
    rw [deductive] ; simp only [refines_def, and_congr_right_iff,List.forall_iff_forall_mem, List.mem_attach, true_implies, Subtype.forall]

lemma supported_nnil {A : GSN} : supported A → A ≠ .nil :=
by intros ; cases A with | nil =>  contradiction | _=> simp only [ne_eq, not_false_eq_true]

theorem proof_of_root : ∀ A : GSN, (h : supported A) → deductive A → ⟦A.root (supported_nnil h)⟧ :=
by
  intros A
  induction A with
  | nil => intros ; contradiction
  | evd _ _ => intros ; rwa [GSN.root]
  | strategy g children ih =>
    intros support deduct
    cases children with
    | nil => contradiction
    | cons x xs =>
      rw [GSN.supported_cons] at support ; rw [GSN.strategy_root] ; rw [strat_deductive_iff] at deduct
      cases' deduct with refinement children_deductive
      apply refinement
      intros g' hg'; rw [mem_roots_cons] at hg'
      cases hg' with
      | inl h =>
        cases' h with h h' ; rw [←h']
        have mem : x ∈ x::xs := List.Mem.head xs
        exact ih x mem (support.2 x mem) (children_deductive x mem)
      | inr h =>
        rcases h with ⟨x',h,xmem,h''⟩ ; rw [← h'']
        have mem : x' ∈ x::xs := List.mem_cons_of_mem x xmem
        exact ih x' mem (support.2 x' mem) (children_deductive x' mem)

end GSN
