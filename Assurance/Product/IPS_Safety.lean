
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

opaque MIPS : LTS
opaque AlarmSafe : CTL

-- Evidence --
axiom noViolationsEvd : V MIPS AlarmSafe = true
axiom verifierSoundEvd : ∀ M' : LTS, ∀ P' : CTL, V M' P' = true ↔ execs M' ⊆ words P'
axiom specCorrectEvd :  words AlarmSafe = TargetProperty

-- Predicated --
def Refines : Set Traces × Set Traces → Prop :=
  λ ⟨S,T⟩ => S ⊆ T

def InputsCorrect : LTS × CTL → Prop :=
λ ⟨M,P⟩ => execs M = AllBehaviours ∧ words P = TargetProperty

def Verified : LTS × CTL → Prop := λ ⟨M,P⟩ => V M P = true

def VerifierSound : Prop := ∀ M' : LTS, ∀ P' : CTL, V M' P' = true ↔ execs M' ⊆ words P'

open scoped Goal GSN

def IPS_Safety : GSN :=
  Refines ⬝ ⟨AllBehaviours,TargetProperty⟩ ⇐                 -- G0
    [ InputsCorrect ⬝ ⟨MIPS,AlarmSafe⟩ ⇐ [],                   -- G1
      Verified ⬝ ⟨MIPS,AlarmSafe⟩ ↼ noViolationsEvd,          -- G3
      VerifierSound ↼ verifierSoundEvd                       -- G4
    ]
