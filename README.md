Formalized Metatheory for Product and Product-Line Assurance Cases (GSN)
============================
This project established formal semantics of Assurance Cases (ACs) in the style of Goal Structuring Notation (GSN), extended for software Product Lines (PLs).

## Setup

* Install [Lean 4](https://lean-lang.org/), including [elan](https://github.com/leanprover/elan). We also recommend [Lean's VSCode extension](https://lean-lang.org/lean4/doc/quickstart.html)

After cloning the repository:

1. Run `lake exe cache get` to download mathlib. This may take several minutes.
2. Run `lake build` to build the repository. 
3. Use a supported editor (e.g., VSCode) to inspect the formalization manually.