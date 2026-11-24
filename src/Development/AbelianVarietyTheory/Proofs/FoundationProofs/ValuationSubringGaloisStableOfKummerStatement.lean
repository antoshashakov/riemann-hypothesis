module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummer
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.mem_valuationSubring_galois_iff_of_kummer_stable : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  first | exact @GlobalTheory.valuationSubring_galois_stable_of_kummer | exact GlobalTheory.valuationSubring_galois_stable_of_kummer | (intros; apply GlobalTheory.valuationSubring_galois_stable_of_kummer <;> assumption)
