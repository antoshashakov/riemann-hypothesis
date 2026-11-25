module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Mathlib.NumberTheory.NumberField.Basic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace GlobalTheory.NonzeroSmulMem

open NumberField

theorem exists_ne_zero_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

end GlobalTheory.NonzeroSmulMem
