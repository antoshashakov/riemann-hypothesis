module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLattice
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.divisionAlgebra_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι → Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B → Module.finrank ℤ X = 0 := by
  first | exact @GlobalTheory.divAlg_order_no_small_lattice | exact GlobalTheory.divAlg_order_no_small_lattice | (intros; apply GlobalTheory.divAlg_order_no_small_lattice <;> assumption)
