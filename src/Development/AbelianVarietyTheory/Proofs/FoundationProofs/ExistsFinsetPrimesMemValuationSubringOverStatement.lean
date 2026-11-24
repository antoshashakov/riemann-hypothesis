module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOver
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_finset_primes_mem_valuationSubring_over : ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F), ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  first | exact @GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | exact GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | (intros; apply GlobalTheory.exists_finset_primes_forall_mem_valuationSubring <;> assumption)
