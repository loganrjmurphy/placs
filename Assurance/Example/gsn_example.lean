import Assurance.Product.GSN

noncomputable section

-- Uninterpreted Types --
opaque CTL : Type
opaque LTS : Type
opaque Traces : Type

axiom CTL.inhabited : Inhabited CTL
axiom LTS.inhabited : Inhabited LTS

noncomputable instance : Inhabited CTL := CTL.inhabited
noncomputable instance : Inhabited LTS := LTS.inhabited

-- Uninterpreted Functions --
opaque words : CTL → Set Traces
opaque execs : LTS → Set Traces
opaque V : LTS → CTL → Bool

-- Objects --
opaque AllBehaviours : Set Traces
opaque TargetProperty : Set Traces

opaque M_SYS : LTS
opaque ALARM_SPEC : CTL

-- Evidence --
axiom noViolationsEvd : V M_SYS ALARM_SPEC = true
axiom verifierSoundEvd : ∀ M' : LTS, ∀ P' : CTL, V M' P' = true ↔ execs M' ⊆ words P'
axiom specCorrectEvd :  words ALARM_SPEC = TargetProperty

-- Predicated --
def Inclusion : Set Traces × Set Traces → Prop :=
  λ ⟨S,T⟩ => S ⊆ T

def modelCorrect : LTS × Set Traces → Prop :=
  λ ⟨M,B⟩ => execs M = B

def specCorrect : CTL × Set Traces → Prop :=
  λ ⟨φ,P⟩ => words φ = P

def Verified : LTS × CTL → Prop := λ ⟨M,P⟩ => V M P = true

def VerifierSound : Prop := ∀ M' : LTS, ∀ P' : CTL, V M' P' = true ↔ execs M' ⊆ words P'

def gsn_example : GSN :=
  .strategy (.pred Inclusion ⟨AllBehaviours,TargetProperty⟩)
    [ (.strategy (.pred modelCorrect ⟨M_SYS,AllBehaviours⟩) []),
      (.evd (.pred specCorrect ⟨ALARM_SPEC,TargetProperty⟩) specCorrectEvd),
      (.evd (.pred Verified ⟨M_SYS,ALARM_SPEC⟩) noViolationsEvd),
      (.evd (.atom VerifierSound) verifierSoundEvd)
    ]
