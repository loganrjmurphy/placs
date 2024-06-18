import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
set_option autoImplicit false

/-
This file defines features and configurations -- the basic elements of variability modeling.
-/

namespace SPL

/-
A type `F` is a `FeatureSet` if it is finite and has decidable equality
We say that terms of type `F` are "features".
-/
class FeatureSet (α: Type) extends Fintype α where
  dec: DecidableEq α

instance {F : Type} [FeatureSet F] :  DecidableEq F := FeatureSet.dec

instance {n : ℕ} : FeatureSet (Fin n) := .mk inferInstance

-- a Configuration over `F` is a (finite) set of features
-- of course, any set over a `Fintype` is finite, but the `Finset` API is more convenient
/-- A presence condition (PC) over α is given by a feature expression (i.e., a propositional formula whose atoms are α-terms). In practice α should be a `FeatureSet`-/
inductive PC (α:Type): Type
| all  : PC α
| none : PC α
| atom : α → PC α
| not  : PC α → PC α
| and  : PC α → PC α → PC α
| or   : PC α → PC α → PC α
deriving DecidableEq


-- Identify a feature as an atomic presence condition
instance FeatureSet.toPC {F:Type} [FeatureSet F] : Coe F (PC F) := Coe.mk PC.atom

-- Some notation typeclasses for presence conditions
instance {F : Type} : Top (PC F) := .mk .all
instance {F : Type} : Bot (PC F) := .mk .none
instance {F: Type} : Complement (PC F) := .mk .not
instance {F: Type} : AndOp (PC F) := .mk .and
instance {F: Type} : OrOp (PC F) := .mk .or

/-- A ConfigSpace is a (finite) set of feature configurations -/
abbrev ConfigSpace (F :Type) [FeatureSet F] := Finset (Finset F)

/-- The set of all 2^|F| configurations of features in F -/
abbrev allConfigs (F : Type) [FeatureSet F] : ConfigSpace F := Finset.univ


namespace PC
/--Every PC φ can be mapped to a set of configurations, namely, those configurations which are satisfying assignments of φ -/
@[reducible]
def semantics {F: Type} [FeatureSet F]: PC F → ConfigSpace F
| ⊤ => allConfigs F
| ⊥ => ∅
| .atom f => (allConfigs F).filter (f ∈ .)
| .not pc => (semantics pc)ᶜ
| .and pc₁ pc₂ => (semantics pc₁) ∩ (semantics pc₂)
| .or pc₁ pc₂ => (semantics pc₁) ∪ (semantics pc₂)
end PC

/- A feature model is just a special kind of feature expression, so we just use an alias for `PC` -/
def FeatModel (F : Type) [FeatureSet F] := PC F

/-- Configurations are defined with respect to a feature model over `F` -/
@[reducible]
def Config {F : Type} [FeatureSet F] (Φ : FeatModel F) : Type := { c : Finset F // c ∈ Φ.semantics}

variable {F : Type} [FeatureSet F] {Φ : FeatModel F}

instance : Fintype (Config Φ) := Subtype.fintype (. ∈ Φ.semantics)

namespace Config

def features (c : Config Φ) : Finset F := c.val

end Config

namespace PC
notation "⦃" p "⦄" => semantics p

def imp (p q : PC F) : PC F :=
  .not p ||| q

infix:55 "⇒" => imp

def iff (p q : PC F) : PC F :=
  (p ⇒ q) &&& (q ⇒ p)

infix:52 "⇔" => iff

@[simp]
lemma imp_semantics {p q : PC F} : ⦃p⇒q⦄ = ⦃p⦄ᶜ ∪ ⦃q⦄ :=
  by rfl

@[simp]
lemma iff_semantics {p q : PC F} : ⦃p⇔q⦄ = (⦃p ⇒ q⦄) ∩ (⦃q ⇒ p⦄) :=
by rfl

/- The satisfiability relation between a configuration `c` and a presence condition `p` i
   defined as set membership w.r.t. the set-theoretic semantics defined above -/

variable {Φ : FeatModel F}

@[reducible]
def sat (c : Config Φ) (p : PC F) : Prop := c.features ∈ ⦃p⦄

infix:50 (priority:=high) "⊨" => sat


instance {c : Config Φ} {p : PC F} : Decidable (c ⊨ p) := inferInstance

/- Some API for the satisfaction relation -/

lemma sat_def {c : Config Φ} {p : PC F} : c ⊨ p ↔ c.features ∈ ⦃p⦄ := by rfl

lemma sat_univ {c : Config Φ}:  c ⊨ .all :=
  by simp only [Finset.mem_univ]

lemma sat_none {c : Config Φ}:  c ⊨ .none → False  :=
  by simp only [Finset.not_mem_empty, IsEmpty.forall_iff]

lemma sat_atom {c : Config Φ} {f : F}  : c ⊨ f ↔ f ∈ c.features :=
  by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma sat_not  {c : Config Φ} {p : PC F} : c ⊨ ~~~ p ↔ ¬ c ⊨ p :=
  by simp only [Finset.mem_compl, sat_def]

lemma sat_conj {c : Config Φ} {p q : PC F} : c ⊨ p &&& q ↔ c ⊨ p ∧ c ⊨ q :=
  by simp only [Finset.mem_inter, sat_def]

lemma sat_disj {c : Config Φ} {p q : PC F} : c ⊨ p ||| q ↔ c ⊨ p ∨ c ⊨ q :=
  by simp only [Finset.mem_union, sat_def]

lemma sat_imp {c : Config Φ} {p q : PC F} : c ⊨ p ⇒ q ↔ (c ⊨ p →  c ⊨ q) :=
  by simp [sat_def,imp_iff_not_or]

lemma sat_iff  {c : Config Φ} {p q : PC F} : c ⊨ p ⇔ q ↔ (c ⊨ p ↔ c ⊨ q) :=
  by rw (config := {occs := .pos [2]}) [iff_def]
     repeat rw [imp_iff_not_or]
     simp only [sat_def, iff_semantics, imp_semantics, Finset.mem_inter, Finset.mem_union, Finset.mem_compl]

end PC


end SPL
