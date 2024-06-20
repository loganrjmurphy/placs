import Var.Feature.Class

inductive FeatExpr (F : Type) [FeatureSet F] : Type
| all  : FeatExpr F
| none : FeatExpr F
| atom : F → FeatExpr F
| not  : FeatExpr F → FeatExpr F
| and  : FeatExpr F → FeatExpr F → FeatExpr F
| or   : FeatExpr F → FeatExpr F → FeatExpr F
deriving DecidableEq

variable {F : Type} [FeatureSet F]
-- Identify a feature as an atomic presence condition
instance : Coe F (FeatExpr F) := Coe.mk .atom

-- Some notation typeclasses for feature expressions
instance : Top (FeatExpr F) := .mk .all
instance : Bot (FeatExpr F) := .mk .none
instance : Complement (FeatExpr F) := .mk .not
instance : AndOp (FeatExpr F) := .mk .and
instance : OrOp (FeatExpr F) := .mk .or

def imp (p q : FeatExpr F) : FeatExpr F :=
  .not p ||| q

infix:55 "⇒" => imp

def iff (p q : FeatExpr F) : FeatExpr F :=
  (p ⇒ q) &&& (q ⇒ p)

infix:52 "⇔" => iff

/- A feature model is just a special kind of feature expression, so we just use an alias for `FeatExpr` -/
@[reducible]
def FeatModel (F : Type) [FeatureSet F] := FeatExpr F

@[reducible]
def PC (F : Type) [FeatureSet F] := FeatExpr F

-- instance : Union (FeatModel F) := ⟨ λ a b => a ||| b⟩
