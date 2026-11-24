module

public import Mathlib.Algebra.Ring.Units
public import Mathlib.Data.ZMod.Defs
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Finset

noncomputable section

namespace Formalism

def counts {l : ℕ} (Φ : Finset (ZMod l)ˣ) (σ : (ZMod l)ˣ) : Prop := σ ∉ Φ ∧ σ ≠ -1



end Formalism
