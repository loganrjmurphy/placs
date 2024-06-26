import Assurance.GSN.Defs

namespace Goal

@[simp]
lemma atom_semantics {p : Prop} : semantics p = p := rfl

@[simp]
lemma pred_semantics {α : Type} {P : α → Prop} {x : α} : semantics (.pred P x) = P x := rfl

end Goal

namespace GSN

@[simp]
lemma evd_root {g : Goal} {h : ⟦g⟧} : root (.evd g h) nofun = g := rfl

@[simp]
lemma strategy_root {g : Goal} {l : List GSN} : root (.strategy g l) (nofun) = g := rfl

@[simp]
lemma root_none_iff {G : GSN} : G.root? = none ↔ G = .nil := by
  cases G <;> simp only

lemma not_nil_iff_some_root (G : GSN) : G ≠ .nil ↔ (∃ g : Goal, some g = G.root?)  := by
  have := Iff.not <| root_none_iff (G := G)
  rw [← ne_eq, Option.ne_none_iff_exists] at this
  exact (this.symm)

lemma ne_nil_of_some_root {G : GSN} {g : Goal} : (G.root? = some g) →  G ≠ .nil := by
  have := not_nil_iff_some_root G
  intro h ; exact this.mpr (Exists.intro g h.symm)

@[simp]
lemma root_opt_elim {G : GSN} {g : Goal} {h : G ≠ nil} : some g = G.root? ↔ G.root h = g :=
by
  rw [root?]
  cases G with
  | nil => exact False.elim (h rfl)
  | _ => rw [Option.some.injEq] ; tauto

lemma not_mem_roots_nil {g: Goal} : ¬ (g ∈ roots []) :=
  by rw [roots,List.reduceOption_mem_iff,List.map_nil] ; exact List.not_mem_nil (some g)

lemma mem_roots_cons {g : Goal} {x : GSN} {xs : List GSN} : g ∈ roots (x::xs) ↔ (∃ h : x ≠ .nil, x.root h = g) ∨ ∃ (x' : GSN) (h' : x' ≠ .nil), x' ∈ xs ∧ x'.root h' = g :=
  by
  rw [roots,List.reduceOption_mem_iff, List.map_cons, List.mem_cons]
  constructor
  . intro h
    cases h with
    | inl h =>
      left
      have := ne_nil_of_some_root h.symm
      rw [root_opt_elim (h := ne_nil_of_some_root h.symm)] at h ;
      use this
    | inr h =>
      right
      rw [List.mem_map] at h
      rcases h with ⟨w, hw1, hw2⟩
      have : w ≠ .nil := ne_nil_of_some_root hw2
      use w ; use this
      exact ⟨hw1, root_opt_elim.mp (Eq.symm hw2)⟩
  .
    intro h
    cases h with
    | inl h =>
      left
      cases' h with w hw
      exact root_opt_elim.mpr hw
    | inr h =>
      right
      rw [List.mem_map]
      rcases h with ⟨w, hw1, ⟨hw2,hw3⟩⟩
      use w
      exact ⟨ hw2, Eq.symm ((root_opt_elim.mpr) hw3)⟩

@[simp]
lemma undevGoals_roots_inv (l : List Goal) : roots (undevGoals l) = l :=
  by
    rw [roots, undevGoals,List.reduceOption,List.map_map, List.filterMap_map, CompTriple.comp_eq]
    induction l with
    | nil => rfl
    | cons h t ih =>
      simpa only [List.filterMap_cons, Function.comp_apply, List.cons.injEq, true_and]

@[simp]
lemma supported_nil : supported .nil = false := rfl

@[simp]
lemma supported_evd {g : Goal} {h : ⟦g⟧} : supported (.evd g h) = true := by rw [supported]; trivial

@[simp]
lemma supported_empty {g : Goal}  : supported (.strategy g []) = false := rfl

@[simp]
lemma supported_cons {g : Goal} {l : List GSN} : supported (.strategy g l) ↔ l ≠ [] ∧ ∀ x ∈ l, supported x :=
  by cases l <;> rw [supported] <;> simp


@[simp]
lemma refines_def {g : Goal} {l : List GSN} : refines (g,l) ↔ (∀ g' ∈ roots l, ⟦g'⟧) → ⟦g⟧ := Iff.rfl

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
