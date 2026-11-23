module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Coset.Defs
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

noncomputable section

namespace GlobalTheory.LKRes

variable {H : Type} [Group H]

def conv (K : Subgroup H) (f f' : H → ℂ) (x : H) : ℂ :=
  ∑ᶠ q : H ⧸ K, f (Quotient.out q) * f' ((Quotient.out q)⁻¹ * x)

end GlobalTheory.LKRes
