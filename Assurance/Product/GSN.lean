import Mathlib
set_option autoImplicit false

inductive Goal
| atom (p : Prop) : Goal
| pred {α : Type} (P : α → Prop) (x : α) : Goal

instance : Coe Prop Goal := ⟨Goal.atom⟩

def semantics : Goal → Prop
| .atom p => p
| .pred P x => P x

notation "⟦"G"⟧" => semantics G

namespace Goal
lemma semantics_atom {p : Prop} : semantics p = p := rfl
lemma semantics_pred {α : Type} {P : α → Prop} {x : α} : semantics (.pred P x) = P x := rfl

scoped infix:81 "⬝" => Goal.pred

end Goal


inductive GSN
| nil : GSN
| evd : Π g : Goal, ⟦g⟧ → GSN
| decomp : Goal → List GSN → GSN


namespace GSN
scoped infix:80 "⇐" => GSN.decomp
scoped infix:80 "↼" => GSN.evd

/-- Handwritten induction principle for GSN trees to simplify proofs about nested inductive trees. To be replaced by more systematic methods -/
axiom inductionOn
  (motive : GSN → Prop)
  (nil : motive nil)
  (evd : ∀ (g : Goal) (e : ⟦g⟧), motive (GSN.evd g e))
  (decomp :
     ∀ (g : Goal) (children : List GSN),
         (∀ (g : GSN), g ∈ children → motive g)
            → motive (GSN.decomp g children))
  : Π (G : GSN), motive G

@[reducible]
def nnil : GSN → Bool
| .nil => false
| .evd _ _ => true
| .decomp _ _ => true

lemma nnil_def_true {A : GSN} : A.nnil = true ↔ A ≠ GSN.nil := by cases A <;> simp
lemma nnil_def_false {A : GSN} : A.nnil =false ↔ A = GSN.nil := by cases A <;> simp

def root? : GSN → Option Goal
| .nil => none
| .evd g _ => g
| .decomp g _ => g

def root : Π (G : GSN), G.nnil → Goal
| .nil, h => False.elim <| by rw [nnil] at h ; simp at h
| .evd g _, _ => g
| .decomp g _, _ => g

def root_evd {g : Goal} {h : ⟦g⟧} : root (g ↼ h) (by rfl) = g := rfl
def root_decomp {g : Goal} {l : List GSN} : root (g ⇐ l) (by rfl) = g := rfl

lemma root_option_elim {G : GSN} {g : Goal} : G.root? = some g ↔ (∃ h : G.nnil, G.root h = g) :=
  by cases G with
     | nil => simp only [GSN.root?,ne_eq, not_true_eq_false, IsEmpty.exists_iff]
     | evd _ _ => simp only [GSN.root?,Option.some.injEq, ne_eq, not_false_eq_true,exists_true_left,GSN.root]
     | decomp g gs => simp only [GSN.root?, Option.some.injEq, ne_eq, not_false_eq_true,exists_const,GSN.root]

def supported : GSN → Bool
| .nil => False
| .evd _ _ => True
| .decomp _ [] => False
| .decomp _ (h::t) => (h::t).attach.all (λ ⟨x,_ ⟩ => supported x)

lemma supported_nil : supported .nil = false := rfl
lemma supported_evd {g : Goal} {h : ⟦g⟧} : supported (.evd g h) = true := by rw [supported]; trivial
lemma supported_empty {g : Goal}  : supported (.decomp g []) = false := rfl
lemma supported_cons {g : Goal} {l : List GSN} : supported (.decomp g l) ↔ l ≠ [] ∧ ∀ x ∈ l, supported x :=
  by cases l <;> rw [supported] <;> simp


def roots (l : List GSN) : List Goal := l.map GSN.root? |> List.reduceOption

lemma not_mem_roots_nil {g: Goal} : ¬ (g ∈ roots []) := by rw [roots]; simp only [List.map_nil, List.reduceOption_nil, List.not_mem_nil, not_false_eq_true]
lemma mem_roots_cons {g : Goal} {x : GSN} {xs : List GSN} : g ∈ roots (x::xs) ↔ (∃ h : x.nnil, x.root h = g) ∨ ∃ (x' : GSN) (h' : x'.nnil), x' ∈ xs ∧  x'.root h' = g :=
  by
  rw [roots,List.reduceOption_mem_iff]; simp only [List.map_cons, List.mem_cons, List.mem_map]
  rw [← root_option_elim]
  constructor
  . intro h
    cases h with
    | inl h => left ; symm at h; exact h
    | inr h => right ; rcases h with ⟨w, hw1,hw2⟩; use w; simp only [true_and, hw1]; rwa [root_option_elim] at hw2
  . intro h
    cases h with
    | inl h => left ; symm at h ; exact h
    | inr h => right ; rcases h with ⟨w, hw1,⟨hw2,hw3⟩⟩; use w ; rw [root_option_elim]; simp_all only [true_and, hw3, exists_const]

def refines (g : Goal) (l : List Goal) : Prop := (∀ g' ∈ l, ⟦g'⟧) → ⟦g⟧

def deductive : GSN → Prop
| .nil => False
| .evd _ _ => True
| .decomp g children => refines g (roots children) ∧ children.attach.Forall (λ ⟨x,_⟩ => deductive x)

lemma not_deductive_nil : ¬ GSN.nil.deductive  := λ h => False.elim h
lemma deductive_evd {g : Goal} {h : ⟦g⟧} : (g ↼ h).deductive := by rw [deductive]; trivial

lemma deductive_evd_eq {g : Goal} {h : ⟦g⟧} : (g ↼ h).deductive = True := by rw [deductive]

lemma deductive_decomp {g : Goal} {l : List GSN}  : (g ⇐ l).deductive ↔ refines g (roots l) ∧ ∀ x ∈ l, deductive x :=
  by rw [deductive, List.forall_iff_forall_mem]
     simp only [List.mem_attach, forall_true_left, Subtype.forall]

lemma supported_nnil {A : GSN} : supported A → A.nnil :=
by intros ; cases A with | nil =>  contradiction | _=> simp only [ne_eq, not_false_eq_true]


theorem proof_of_root : ∀ A : GSN, (h : supported A) → deductive A → ⟦A.root (supported_nnil h)⟧ :=
by
  intros A
  induction A using GSN.inductionOn with
  | nil => intros ; contradiction
  | evd _ _ => intros ; rwa [GSN.root]
  | decomp g children ih =>
    intros support deduct
    cases children with
    | nil => contradiction
    | cons x xs =>
      rw [GSN.supported_cons] at support ; rw [GSN.root_decomp] ; rw [deductive_decomp] at deduct
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
