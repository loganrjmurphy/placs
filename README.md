Formalized Metatheory for Product and Product-Line Assurance Cases (GSN)
============================
This project established formal semantics of Assurance Cases (ACs) in the style of Goal Structuring Notation (GSN), extended for software Product Lines (PLs).

## Setup

* Install [Lean 4](https://lean-lang.org/), including [elan](https://github.com/leanprover/elan). We also recommend [Lean's VSCode extension](https://lean-lang.org/lean4/doc/quickstart.html)

After cloning the repository:

1. Run `lake exe cache get` to download mathlib
2. Run `lake build` to build the repository. This will verify all proofs in the `SPL` and `Assurance` directories.  You should see something like: 
```
[3114/4452] Building SPL.Config
[4441/4452] Building Assurance.Product.GSN
[4442/4452] Building SPL.Lifting
[4443/4452] Building SPL
[4443/4452] Building SPL.Data
[4446/4452] Building Assurance.Product.Template
[4446/4452] Building Assurance.ProductLine.vGSN
[4447/4452] Building Assurance.Product.Analytic
[4448/4452] Building Assurance.ProductLine.vTemplate
[4450/4452] Building Assurance.ProductLine.Analytic
[4451/4452] Building Assurance
```
3. Use a supported editor (e.g., VSCode) to inspect the formalization manually.